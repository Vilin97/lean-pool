/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemma

/-!
# Carrier-level zigzag identities

The zigzag laws of a Mod-internal duality datum are stated at the
multi-tensor level, where the wide-coequalizer presentation keeps
them associativity-free.  Their consumers work on the carriers
`M.X` and `M'.X`, through the binary relative tensor alone: insert
the copairing beside the carrier, contract the crossing pair
through the descended pairing, and let the resulting scalar act on
the inserted half.  This file identifies both triangle composites
with their carrier forms, unconditionally, and derives the
carrier-level triangle identities from the multi-level laws and
conversely.

* `zigContract`, `zagContract`: the carrier contractions, morphisms
  out of `modTensor A M M' ⊗ M.X` and `M'.X ⊗ modTensor A M M'`
  descended along the whiskered module-tensor coequalizers, with
  defining equations isolating `modTensorπ A M' M ≫ p`.
* `zigComposite_eq_carrier`, `zagComposite_eq_carrier`: the
  multi-level triangle composites are the singleton conjugates of
  the carrier words.  No zigzag hypothesis enters.
* `zigzag_carrier_zig`, `zigzag_carrier_zag`: the carrier triangle
  identities of a zigzag datum, with quantified variants for any
  solution of the contraction's defining equation.
* `modZigzagDatum_of_carrier`: the converse packaging, producing
  the multi-level laws from the carrier-level identities.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Conjugation by an isomorphism preserves and reflects the
identity. -/
theorem iso_conj_id_iff [Category.{v} D]
    {X Y : D} (i : X ≅ Y) {g : Y ⟶ Y} :
    i.hom ≫ g ≫ i.inv = 𝟙 X ↔ g = 𝟙 Y := by
  constructor
  · intro h
    have h2 := congrArg (fun t => i.inv ≫ t ≫ i.hom) h
    simpa using h2
  · intro h
    rw [h, Category.id_comp, Iso.hom_inv_id]

/-! ## The singleton comparison as a conjugation -/

section Single

/-- The singleton projection against the comparison iso: the right
unitor of the carrier. -/
@[reassoc]
theorem modMultiπ_single
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A]
    (X : Mod D A) :
    modMultiπ A [X] ≫ (modMultiSingle A X).hom = (ρ_ X.X).hom := by
  show (modMultiTriv A (modSlots_singleton A X)).inv ≫
      (modMultiTriv A (modSlots_singleton A X)).hom ≫
      (ρ_ X.X).hom = (ρ_ X.X).hom
  erw [Iso.inv_hom_id_assoc]

/-- Recognise a singleton conjugate: a multi-level morphism whose
projection matches a carrier morphism through the unitor is the
conjugate of that morphism. -/
theorem eq_single_conj [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A]
    {X Y : Mod D A}
    {f : modMulti A [X] ⟶ modMulti A [Y]} {g : X.X ⟶ Y.X}
    (h : modMultiπ A [X] ≫ f ≫ (modMultiSingle A Y).hom =
      (ρ_ X.X).hom ≫ g) :
    f = (modMultiSingle A X).hom ≫ g ≫
      (modMultiSingle A Y).inv := by
  apply modMulti_hom_ext
  have h' : (modMultiπ A [X] ≫ f ≫ (modMultiSingle A Y).hom) ≫
      (modMultiSingle A Y).inv =
    ((ρ_ X.X).hom ≫ g) ≫ (modMultiSingle A Y).inv :=
    congrArg (fun t => t ≫ (modMultiSingle A Y).inv) h
  have hL : (modMultiπ A [X] ≫ f ≫ (modMultiSingle A Y).hom) ≫
      (modMultiSingle A Y).inv = modMultiπ A [X] ≫ f := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hR : ((ρ_ X.X).hom ≫ g) ≫ (modMultiSingle A Y).inv =
      (ρ_ X.X).hom ≫ g ≫ (modMultiSingle A Y).inv :=
    Category.assoc _ _ _
  exact ((hL.symm.trans h').trans hR).trans
    (modMultiπ_single_assoc A X
      (g ≫ (modMultiSingle A Y).inv)).symm

end Single

/-! ## The zig triangle on the carrier -/

section ZigCarrier

/-- The trailing contraction fold against the singleton
comparison: pair the trailing window, act on the head from the
right. -/
theorem contract3Fold_single
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A) :
    contract3Fold A p M ≫ (modMultiSingle A M).hom =
      (M.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
  have hfold : contract3Fold A p M =
      (M.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
          modTensorπ A M' M ≫ p)) ≫
        actRight A M.X ≫ (modMultiSingle A M).inv := rfl
  have hcancel : ((M.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
          modTensorπ A M' M ≫ p)) ≫
        actRight A M.X ≫ (modMultiSingle A M).inv) ≫
        (modMultiSingle A M).hom =
      (M.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun t => t ≫ (modMultiSingle A M).hom)
    hfold).trans hcancel

/-- A trailing window against the resolved contraction: stripping
the unit seed of the fold, the window meets the carrier
contraction word. -/
theorem window_contract3Fold_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (w : (M.X ⊗ A) ⊗ M'.X ⟶ M.X ⊗ M'.X) :
    ((((M.X ⊗ A) ⊗ M'.X) ◁ (ρ_ M.X).inv) ≫
        ((w ▷ modList A [M]) ≫
          (α_ M.X M'.X (modList A [M])).hom)) ≫
        contract3Fold A p M ≫ (modMultiSingle A M).hom =
      (w ▷ M.X) ≫ (α_ M.X M'.X M.X).hom ≫
        (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
  have h1 := congrArg
    (fun t => ((((M.X ⊗ A) ⊗ M'.X) ◁ (ρ_ M.X).inv) ≫
      ((w ▷ modList A [M]) ≫
        (α_ M.X M'.X (modList A [M])).hom)) ≫ t)
    (contract3Fold_single A p)
  have h2 : ((((M.X ⊗ A) ⊗ M'.X) ◁ (ρ_ M.X).inv) ≫
        ((w ▷ (M.X ⊗ 𝟙_ D)) ≫
          (α_ M.X M'.X (M.X ⊗ 𝟙_ D)).hom)) ≫
        ((M.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
          modTensorπ A M' M ≫ p)) ≫ actRight A M.X) =
      (w ▷ M.X) ≫ (α_ M.X M'.X M.X).hom ≫
        (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
    have hx : ((((M.X ⊗ A) ⊗ M'.X)) ◁ (ρ_ M.X).inv) ≫
        (w ▷ (M.X ⊗ 𝟙_ D)) =
      (w ▷ M.X) ≫ ((M.X ⊗ M'.X) ◁ (ρ_ M.X).inv) :=
      whisker_exchange w (ρ_ M.X).inv
    have hcoh : ((M.X ⊗ M'.X) ◁ (ρ_ M.X).inv) ≫
        (α_ M.X M'.X (M.X ⊗ 𝟙_ D)).hom ≫
        (M.X ◁ (M'.X ◁ (ρ_ M.X).hom)) =
      (α_ M.X M'.X M.X).hom := by
      monoidal
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% hx, reassoc_of% hcoh]
  exact h1.trans h2

/-- The descent condition of the trailing carrier contraction: the
two legs of the crossing pair agree, through the boundary
condition of the fold-level contraction. -/
theorem zigContract_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    (modTensorLegM A M M' ▷ M.X) ≫ (α_ M.X M'.X M.X).hom ≫
        (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X =
      (modTensorLegN A M M' ▷ M.X) ≫ (α_ M.X M'.X M.X).hom ≫
        (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
  have hcond' : ((modTensorLegM A M M' ▷ modList A [M]) ≫
        (α_ M.X M'.X (modList A [M])).hom) ≫
      contract3Fold A p M =
    ((modTensorLegN A M M' ▷ modList A [M]) ≫
        (α_ M.X M'.X (modList A [M])).hom) ≫
      contract3Fold A p M :=
    contract3Fold_boundary_cond A p hp M
  have hmid := congrArg
    (fun t => ((((M.X ⊗ A) ⊗ M'.X)) ◁ (ρ_ M.X).inv) ≫
      t ≫ (modMultiSingle A M).hom) hcond'
  have aM : ((((M.X ⊗ A) ⊗ M'.X) ◁ (ρ_ M.X).inv) ≫
        ((modTensorLegM A M M' ▷ modList A [M]) ≫
          (α_ M.X M'.X (modList A [M])).hom)) ≫
        contract3Fold A p M ≫ (modMultiSingle A M).hom =
      ((((M.X ⊗ A) ⊗ M'.X)) ◁ (ρ_ M.X).inv) ≫
        (((modTensorLegM A M M' ▷ modList A [M]) ≫
          (α_ M.X M'.X (modList A [M])).hom) ≫
          contract3Fold A p M) ≫ (modMultiSingle A M).hom := by
    repeat' erw [Category.assoc]
  have aN : ((((M.X ⊗ A) ⊗ M'.X) ◁ (ρ_ M.X).inv) ≫
        ((modTensorLegN A M M' ▷ modList A [M]) ≫
          (α_ M.X M'.X (modList A [M])).hom)) ≫
        contract3Fold A p M ≫ (modMultiSingle A M).hom =
      ((((M.X ⊗ A) ⊗ M'.X)) ◁ (ρ_ M.X).inv) ≫
        (((modTensorLegN A M M' ▷ modList A [M]) ≫
          (α_ M.X M'.X (modList A [M])).hom) ≫
          contract3Fold A p M) ≫ (modMultiSingle A M).hom := by
    repeat' erw [Category.assoc]
  exact (window_contract3Fold_carrier A p
      (modTensorLegM A M M')).symm.trans
    ((aM.trans (hmid.trans aN.symm)).trans
      (window_contract3Fold_carrier A p (modTensorLegN A M M')))

/-- **The carrier contraction of the zig triangle**: on
`modTensor A M M' ⊗ M.X`, the inserted `M'`-half pairs against
the trailing carrier through the descended pairing and the
resulting scalar acts on the inserted `M`-half from the right.
Descended along the right-whiskered module-tensor coequalizer. -/
noncomputable def zigContract
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    modTensor A M M' ⊗ M.X ⟶ M.X :=
  modTensorWhiskerRDesc A M M' M.X
    ((α_ M.X M'.X M.X).hom ≫
      (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X)
    (zigContract_cond A p hp)

/-- Defining equation of the zig carrier contraction: the pairing
occurrence is isolated as `modTensorπ A M' M ≫ p`. -/
@[reassoc (attr := simp)]
theorem whiskerRight_modTensorπ_zigContract
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    (modTensorπ A M M' ▷ M.X) ≫ zigContract A p hp =
      (α_ M.X M'.X M.X).hom ≫
        (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X :=
  whiskerRight_modTensorπ_whiskerRDesc A M M' M.X _ _

/-- The zig carrier contraction is the unique solution of its
defining equation. -/
theorem zigContract_unique
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    {e : modTensor A M M' ⊗ M.X ⟶ M.X}
    (he : (modTensorπ A M M' ▷ M.X) ≫ e =
      (α_ M.X M'.X M.X).hom ≫
        (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X) :
    e = zigContract A p hp :=
  modTensor_whiskerR_hom_ext A M M' M.X
    (he.trans
      (whiskerRight_modTensorπ_zigContract A p hp).symm)

/-- The inserted pair against the concatenation and trailing
contraction: the multi-level word collapses to the carrier
contraction. -/
theorem pairInv_concat_contract3_single
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    (modMultiPairInv A M M' ▷ modList A [M]) ≫
        modMultiConcatFst A [M, M'] [M] ≫
        modMultiContract3 A p hp M ≫ (modMultiSingle A M).hom =
      (modTensor A M M' ◁ (ρ_ M.X).hom) ≫ zigContract A p hp := by
  apply modTensor_whiskerR_hom_ext A M M' (modList A [M])
  have s1 : (modTensorπ A M M' ▷ modList A [M]) ≫
      (modMultiPairInv A M M' ▷ modList A [M]) =
    (pairResolveInv A M M' ▷ modList A [M]) ≫
      (modMultiπ A [M, M'] ▷ modList A [M]) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      modTensorπ_pairInv, MonoidalCategory.comp_whiskerRight]
  have s2 : (modMultiπ A [M, M'] ▷ modList A [M]) ≫
      modMultiConcatFst A [M, M'] [M] =
    (modListConcat A [M, M'] [M]).hom ≫
      modMultiπ A ([M, M'] ++ [M]) :=
    whiskerRight_modMultiπ_concatFst A [M, M'] [M]
  have s3 : modMultiπ A ([M, M'] ++ [M]) ≫
      modMultiContract3 A p hp M = contract3Fold A p M :=
    modMultiπ_contract3 A p hp M
  rw [reassoc_of% s1, reassoc_of% s2, reassoc_of% s3]
  have hL2 := congrArg
    (fun t => (pairResolveInv A M M' ▷ modList A [M]) ≫
      (modListConcat A [M, M'] [M]).hom ≫ t)
    (contract3Fold_single A p)
  have hnat : ((M.X ◁ (ρ_ M'.X).inv) ▷ (M.X ⊗ 𝟙_ D)) ≫
      ((α_ M.X (M'.X ⊗ 𝟙_ D) (M.X ⊗ 𝟙_ D)).hom ≫
        (M.X ◁ ((α_ M'.X (𝟙_ D) (M.X ⊗ 𝟙_ D)).hom ≫
          (M'.X ◁ (λ_ (M.X ⊗ 𝟙_ D)).hom)))) ≫
      ((M.X ◁ ((M'.X ◁ (ρ_ M.X).hom) ≫
        modTensorπ A M' M ≫ p)) ≫ actRight A M.X) =
    ((M.X ⊗ M'.X) ◁ (ρ_ M.X).hom) ≫ (α_ M.X M'.X M.X).hom ≫
      (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
    have hcoh : ((M.X ◁ (ρ_ M'.X).inv) ▷ (M.X ⊗ 𝟙_ D)) ≫
        (α_ M.X (M'.X ⊗ 𝟙_ D) (M.X ⊗ 𝟙_ D)).hom ≫
        (M.X ◁ (α_ M'.X (𝟙_ D) (M.X ⊗ 𝟙_ D)).hom) ≫
        (M.X ◁ (M'.X ◁ (λ_ (M.X ⊗ 𝟙_ D)).hom)) ≫
        (M.X ◁ (M'.X ◁ (ρ_ M.X).hom)) =
      ((M.X ⊗ M'.X) ◁ (ρ_ M.X).hom) ≫
        (α_ M.X M'.X M.X).hom := by
      monoidal
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% hcoh]
  have hR : (modTensorπ A M M' ▷ (M.X ⊗ 𝟙_ D)) ≫
      (modTensor A M M' ◁ (ρ_ M.X).hom) ≫ zigContract A p hp =
    ((M.X ⊗ M'.X) ◁ (ρ_ M.X).hom) ≫ (α_ M.X M'.X M.X).hom ≫
      (M.X ◁ (modTensorπ A M' M ≫ p)) ≫ actRight A M.X := by
    have hx : (modTensorπ A M M' ▷ (M.X ⊗ 𝟙_ D)) ≫
        (modTensor A M M' ◁ (ρ_ M.X).hom) =
      ((M.X ⊗ M'.X) ◁ (ρ_ M.X).hom) ≫
        (modTensorπ A M M' ▷ M.X) :=
      (whisker_exchange (modTensorπ A M M') (ρ_ M.X).hom).symm
    rw [reassoc_of% hx, whiskerRight_modTensorπ_zigContract]
  exact (hL2.trans hnat).trans hR.symm

/-- The image of a copairing splits into the copairing and the
pair comparison. -/
theorem copairImage_eq [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M') :
    copairImage A c = (η[A] ≫ c) ≫ modMultiPairInv A M M' := by
  simp only [copairImage]
  rw [← Category.assoc]
  rfl

/-- **The zig composite in carrier form**: conjugated by the
singleton comparison, the multi-level zig composite is the
carrier insertion of the copairing followed by the carrier
contraction.  No zigzag law enters. -/
theorem zigComposite_eq_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    zigComposite A c p hp =
      (modMultiSingle A M).hom ≫
        ((λ_ M.X).inv ≫ ((η[A] ≫ c) ▷ M.X) ≫
          zigContract A p hp) ≫
        (modMultiSingle A M).inv := by
  apply eq_single_conj
  have s1 : modMultiπ A [M] ≫ (λ_ (modMulti A [M])).inv =
      (λ_ (modList A [M])).inv ≫ (𝟙_ D ◁ modMultiπ A [M]) :=
    leftUnitor_inv_naturality _
  have s2 : (𝟙_ D ◁ modMultiπ A [M]) ≫
      (copairImage A c ▷ modMulti A [M]) =
    (copairImage A c ▷ modList A [M]) ≫
      (modMulti A [M, M'] ◁ modMultiπ A [M]) :=
    whisker_exchange _ _
  have hbig : modMultiπ A [M] ≫ zigComposite A c p hp ≫
      (modMultiSingle A M).hom =
    (λ_ (modList A [M])).inv ≫
      ((η[A] ≫ c) ▷ modList A [M]) ≫
      ((modMultiPairInv A M M' ▷ modList A [M]) ≫
        modMultiConcatFst A [M, M'] [M] ≫
        modMultiContract3 A p hp M ≫
        (modMultiSingle A M).hom) := by
    simp only [zigComposite, Category.assoc]
    rw [reassoc_of% s1, reassoc_of% s2,
      whiskerLeft_modMultiπ_concat_assoc, copairImage_eq,
      MonoidalCategory.comp_whiskerRight]
    repeat' erw [Category.assoc]
  have hcore := pairInv_concat_contract3_single A p hp
  have hfin : (λ_ (M.X ⊗ 𝟙_ D)).inv ≫
      ((η[A] ≫ c) ▷ (M.X ⊗ 𝟙_ D)) ≫
      ((modTensor A M M' ◁ (ρ_ M.X).hom) ≫
        zigContract A p hp) =
    (ρ_ M.X).hom ≫ (λ_ M.X).inv ≫ ((η[A] ≫ c) ▷ M.X) ≫
      zigContract A p hp := by
    have s5 : ((η[A] ≫ c) ▷ (M.X ⊗ 𝟙_ D)) ≫
        (modTensor A M M' ◁ (ρ_ M.X).hom) =
      (𝟙_ D ◁ (ρ_ M.X).hom) ≫ ((η[A] ≫ c) ▷ M.X) :=
      (whisker_exchange _ _).symm
    have s6 : (λ_ (M.X ⊗ 𝟙_ D)).inv ≫
        (𝟙_ D ◁ (ρ_ M.X).hom) =
      (ρ_ M.X).hom ≫ (λ_ M.X).inv := by
      monoidal
    rw [reassoc_of% s5, reassoc_of% s6]
  exact hbig.trans
    ((congrArg (fun t => (λ_ (modList A [M])).inv ≫
      ((η[A] ≫ c) ▷ modList A [M]) ≫ t) hcore).trans hfin)

/-- The carrier zig identity from the multi-level zig law. -/
theorem zig_carrier_of_multi
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (h : zigComposite A c p hp = 𝟙 (modMulti A [M])) :
    (λ_ M.X).inv ≫ ((η[A] ≫ c) ▷ M.X) ≫ zigContract A p hp =
      𝟙 M.X :=
  (iso_conj_id_iff (modMultiSingle A M)).mp
    ((zigComposite_eq_carrier A c p hp).symm.trans h)

/-- The multi-level zig law from the carrier zig identity. -/
theorem multi_of_zig_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (h : (λ_ M.X).inv ≫ ((η[A] ≫ c) ▷ M.X) ≫
      zigContract A p hp = 𝟙 M.X) :
    zigComposite A c p hp = 𝟙 (modMulti A [M]) := by
  rw [zigComposite_eq_carrier A c p hp, h, Category.id_comp,
    Iso.hom_inv_id]

end ZigCarrier

/-! ## The zag triangle on the carrier -/

section ZagCarrier

/-- The leading contraction fold against the singleton
comparison: pair the leading window, act on the remainder from
the left. -/
theorem contract3LFold_single
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A) :
    contract3LFold A p M' ≫ (modMultiSingle A M').hom =
      (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        (A ◁ (ρ_ M'.X).hom) ≫ actLeft A M'.X := by
  have hfold : contract3LFold A p M' =
      (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        ((α_ A M'.X (𝟙_ D)).inv ≫
          (actLeft A M'.X ▷ (𝟙_ D))) ≫
        modMultiπ A [M'] := rfl
  have hstep : ((α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        ((α_ A M'.X (𝟙_ D)).inv ≫
          (actLeft A M'.X ▷ (𝟙_ D))) ≫
        modMultiπ A [M']) ≫ (modMultiSingle A M').hom =
      (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        ((α_ A M'.X (𝟙_ D)).inv ≫
          (actLeft A M'.X ▷ (𝟙_ D))) ≫
        (modMultiπ A [M'] ≫ (modMultiSingle A M').hom) := by
    repeat' erw [Category.assoc]
  have hmid := congrArg
    (fun t => (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
      ((α_ A M'.X (𝟙_ D)).inv ≫
        (actLeft A M'.X ▷ (𝟙_ D))) ≫ t)
    (modMultiπ_single A M')
  have htail : (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
      ((α_ A M'.X (𝟙_ D)).inv ≫
        (actLeft A M'.X ▷ (𝟙_ D))) ≫ (ρ_ M'.X).hom =
    (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
      (A ◁ (ρ_ M'.X).hom) ≫ actLeft A M'.X := by
    have hcoh : (α_ A M'.X (𝟙_ D)).inv ≫
        (ρ_ (A ⊗ M'.X)).hom = A ◁ (ρ_ M'.X).hom := by
      monoidal
    have h1 : ((α_ A M'.X (𝟙_ D)).inv ≫
        (actLeft A M'.X ▷ (𝟙_ D))) ≫ (ρ_ M'.X).hom =
      (A ◁ (ρ_ M'.X).hom) ≫ actLeft A M'.X := by
      rw [Category.assoc, rightUnitor_naturality,
        reassoc_of% hcoh]
    rw [h1]
  exact ((congrArg (fun t => t ≫ (modMultiSingle A M').hom)
    hfold).trans hstep).trans (hmid.trans htail)

/-- A leading window against the resolved contraction: stripping
the unit seed of the fold, the window meets the carrier
contraction word. -/
theorem window_contract3LFold_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (w : (M.X ⊗ A) ⊗ M'.X ⟶ M.X ⊗ M'.X) :
    (M'.X ◁ ((ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
        ((w ▷ modList A []) ≫
          (α_ M.X M'.X (modList A [])).hom))) ≫
        contract3LFold A p M' ≫ (modMultiSingle A M').hom =
      (M'.X ◁ w) ≫ (α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X := by
  have h1 := congrArg
    (fun t => (M'.X ◁ ((ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
      ((w ▷ modList A []) ≫
        (α_ M.X M'.X (modList A [])).hom))) ≫ t)
    (contract3LFold_single A p)
  have h2 : (M'.X ◁ ((ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
        ((w ▷ (𝟙_ D)) ≫ (α_ M.X M'.X (𝟙_ D)).hom))) ≫
        ((α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
          ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
          (A ◁ (ρ_ M'.X).hom) ≫ actLeft A M'.X) =
      (M'.X ◁ w) ≫ (α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X := by
    have hw : (ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
        ((w ▷ (𝟙_ D)) ≫ (α_ M.X M'.X (𝟙_ D)).hom) =
      w ≫ (ρ_ (M.X ⊗ M'.X)).inv ≫
        (α_ M.X M'.X (𝟙_ D)).hom := by
      have hnatw : (ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
          (w ▷ (𝟙_ D)) = w ≫ (ρ_ (M.X ⊗ M'.X)).inv :=
        (rightUnitor_inv_naturality w).symm
      rw [← Category.assoc, hnatw, Category.assoc]
    have hx : ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        (A ◁ (ρ_ M'.X).hom) =
      ((M'.X ⊗ M.X) ◁ (ρ_ M'.X).hom) ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) :=
      (whisker_exchange (modTensorπ A M' M ≫ p)
        (ρ_ M'.X).hom).symm
    have hcoh : (M'.X ◁ (ρ_ (M.X ⊗ M'.X)).inv) ≫
        (M'.X ◁ (α_ M.X M'.X (𝟙_ D)).hom) ≫
        (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((M'.X ⊗ M.X) ◁ (ρ_ M'.X).hom) =
      (α_ M'.X M.X M'.X).inv := by
      monoidal
    rw [hw]
    simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rw [reassoc_of% hx, reassoc_of% hcoh]
  exact h1.trans h2

/-- The descent condition of the leading carrier contraction: the
two legs of the crossing pair agree, through the boundary
condition of the fold-level contraction. -/
theorem zagContract_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    (M'.X ◁ modTensorLegM A M M') ≫ (α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X =
      (M'.X ◁ modTensorLegN A M M') ≫ (α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X := by
  have hcond' : (M'.X ◁ ((modTensorLegM A M M' ▷
        modList A []) ≫
        (α_ M.X M'.X (modList A [])).hom)) ≫
      contract3LFold A p M' =
    (M'.X ◁ ((modTensorLegN A M M' ▷ modList A []) ≫
        (α_ M.X M'.X (modList A [])).hom)) ≫
      contract3LFold A p M' :=
    contract3LFold_boundary_cond A p hp M'
  have hmid := congrArg
    (fun t => (M'.X ◁ (ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv) ≫
      t ≫ (modMultiSingle A M').hom) hcond'
  have aM : (M'.X ◁ ((ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
        ((modTensorLegM A M M' ▷ modList A []) ≫
          (α_ M.X M'.X (modList A [])).hom))) ≫
        contract3LFold A p M' ≫ (modMultiSingle A M').hom =
      (M'.X ◁ (ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv) ≫
        ((M'.X ◁ ((modTensorLegM A M M' ▷ modList A []) ≫
          (α_ M.X M'.X (modList A [])).hom)) ≫
          contract3LFold A p M') ≫
        (modMultiSingle A M').hom := by
    rw [MonoidalCategory.whiskerLeft_comp]
    repeat' erw [Category.assoc]
  have aN : (M'.X ◁ ((ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv ≫
        ((modTensorLegN A M M' ▷ modList A []) ≫
          (α_ M.X M'.X (modList A [])).hom))) ≫
        contract3LFold A p M' ≫ (modMultiSingle A M').hom =
      (M'.X ◁ (ρ_ ((M.X ⊗ A) ⊗ M'.X)).inv) ≫
        ((M'.X ◁ ((modTensorLegN A M M' ▷ modList A []) ≫
          (α_ M.X M'.X (modList A [])).hom)) ≫
          contract3LFold A p M') ≫
        (modMultiSingle A M').hom := by
    rw [MonoidalCategory.whiskerLeft_comp]
    repeat' erw [Category.assoc]
  exact (window_contract3LFold_carrier A p
      (modTensorLegM A M M')).symm.trans
    ((aM.trans (hmid.trans aN.symm)).trans
      (window_contract3LFold_carrier A p
        (modTensorLegN A M M')))

/-- **The carrier contraction of the zag triangle**: on
`M'.X ⊗ modTensor A M M'`, the leading carrier pairs against the
inserted `M`-half through the descended pairing and the resulting
scalar acts on the inserted `M'`-half from the left.  Descended
along the left-whiskered module-tensor coequalizer. -/
noncomputable def zagContract
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    M'.X ⊗ modTensor A M M' ⟶ M'.X :=
  modTensorWhiskerDesc A M M' M'.X
    ((α_ M'.X M.X M'.X).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X)
    (zagContract_cond A p hp)

/-- Defining equation of the zag carrier contraction: the pairing
occurrence is isolated as `modTensorπ A M' M ≫ p`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_modTensorπ_zagContract
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    (M'.X ◁ modTensorπ A M M') ≫ zagContract A p hp =
      (α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X :=
  whiskerLeft_modTensorπ_whiskerDesc A M M' M'.X _ _

/-- The zag carrier contraction is the unique solution of its
defining equation. -/
theorem zagContract_unique
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    {e : M'.X ⊗ modTensor A M M' ⟶ M'.X}
    (he : (M'.X ◁ modTensorπ A M M') ≫ e =
      (α_ M'.X M.X M'.X).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X) :
    e = zagContract A p hp :=
  modTensor_whisker_hom_ext A M M' M'.X
    (he.trans
      (whiskerLeft_modTensorπ_zagContract A p hp).symm)

/-- The inserted pair against the concatenation and leading
contraction: the multi-level word collapses to the carrier
contraction. -/
theorem pairInv_concat_contract3L_single
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    (modList A [M'] ◁ modMultiPairInv A M M') ≫
        (modMultiπ A [M'] ▷ modMulti A [M, M']) ≫
        modMultiConcat A [M'] [M, M'] ≫
        modMultiContract3L A p hp M' ≫
        (modMultiSingle A M').hom =
      ((ρ_ M'.X).hom ▷ modTensor A M M') ≫
        zagContract A p hp := by
  apply modTensor_whisker_hom_ext A M M' (modList A [M'])
  have s1 : (modList A [M'] ◁ modTensorπ A M M') ≫
      (modList A [M'] ◁ modMultiPairInv A M M') =
    (modList A [M'] ◁ pairResolveInv A M M') ≫
      (modList A [M'] ◁ modMultiπ A [M, M']) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      modTensorπ_pairInv, MonoidalCategory.whiskerLeft_comp]
  have s2 : (modList A [M'] ◁ modMultiπ A [M, M']) ≫
      (modMultiπ A [M'] ▷ modMulti A [M, M']) =
    (modMultiπ A [M'] ▷ modList A [M, M']) ≫
      (modMulti A [M'] ◁ modMultiπ A [M, M']) :=
    whisker_exchange _ _
  have s4 : (modMultiπ A [M'] ▷ modList A [M, M']) ≫
      modMultiConcatFst A [M'] [M, M'] =
    (modListConcat A [M'] [M, M']).hom ≫
      modMultiπ A ([M'] ++ [M, M']) :=
    whiskerRight_modMultiπ_concatFst A [M'] [M, M']
  have s5 : modMultiπ A ([M'] ++ [M, M']) ≫
      modMultiContract3L A p hp M' = contract3LFold A p M' :=
    modMultiπ_contract3L A p hp M'
  rw [reassoc_of% s1, reassoc_of% s2,
    whiskerLeft_modMultiπ_concat_assoc, reassoc_of% s4,
    reassoc_of% s5]
  have hL2 := congrArg
    (fun t => (modList A [M'] ◁ pairResolveInv A M M') ≫
      (modListConcat A [M'] [M, M']).hom ≫ t)
    (contract3LFold_single A p)
  have hnat : ((M'.X ⊗ 𝟙_ D) ◁ (M.X ◁ (ρ_ M'.X).inv)) ≫
      ((α_ M'.X (𝟙_ D) (M.X ⊗ (M'.X ⊗ 𝟙_ D))).hom ≫
        (M'.X ◁ (λ_ (M.X ⊗ (M'.X ⊗ 𝟙_ D))).hom)) ≫
      ((α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        (A ◁ (ρ_ M'.X).hom) ≫ actLeft A M'.X) =
    ((ρ_ M'.X).hom ▷ (M.X ⊗ M'.X)) ≫
      (α_ M'.X M.X M'.X).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X := by
    have hx : ((modTensorπ A M' M ≫ p) ▷ (M'.X ⊗ 𝟙_ D)) ≫
        (A ◁ (ρ_ M'.X).hom) =
      ((M'.X ⊗ M.X) ◁ (ρ_ M'.X).hom) ≫
        ((modTensorπ A M' M ≫ p) ▷ M'.X) :=
      (whisker_exchange (modTensorπ A M' M ≫ p)
        (ρ_ M'.X).hom).symm
    have hcoh : ((M'.X ⊗ 𝟙_ D) ◁ (M.X ◁ (ρ_ M'.X).inv)) ≫
        (α_ M'.X (𝟙_ D) (M.X ⊗ (M'.X ⊗ 𝟙_ D))).hom ≫
        (M'.X ◁ (λ_ (M.X ⊗ (M'.X ⊗ 𝟙_ D))).hom) ≫
        (α_ M'.X M.X (M'.X ⊗ 𝟙_ D)).inv ≫
        ((M'.X ⊗ M.X) ◁ (ρ_ M'.X).hom) =
      ((ρ_ M'.X).hom ▷ (M.X ⊗ M'.X)) ≫
        (α_ M'.X M.X M'.X).inv := by
      monoidal
    repeat' erw [Category.assoc]
    rw [reassoc_of% hx, reassoc_of% hcoh]
  have hR : ((M'.X ⊗ 𝟙_ D) ◁ modTensorπ A M M') ≫
      ((ρ_ M'.X).hom ▷ modTensor A M M') ≫
      zagContract A p hp =
    ((ρ_ M'.X).hom ▷ (M.X ⊗ M'.X)) ≫
      (α_ M'.X M.X M'.X).inv ≫
      ((modTensorπ A M' M ≫ p) ▷ M'.X) ≫ actLeft A M'.X := by
    have hx2 : ((M'.X ⊗ 𝟙_ D) ◁ modTensorπ A M M') ≫
        ((ρ_ M'.X).hom ▷ modTensor A M M') =
      ((ρ_ M'.X).hom ▷ (M.X ⊗ M'.X)) ≫
        (M'.X ◁ modTensorπ A M M') :=
      whisker_exchange _ _
    rw [reassoc_of% hx2, whiskerLeft_modTensorπ_zagContract]
  exact (hL2.trans hnat).trans hR.symm

/-- **The zag composite in carrier form**: conjugated by the
singleton comparison, the multi-level zag composite is the
carrier insertion of the copairing followed by the carrier
contraction.  No zigzag law enters. -/
theorem zagComposite_eq_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A]) :
    zagComposite A c p hp =
      (modMultiSingle A M').hom ≫
        ((ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ c)) ≫
          zagContract A p hp) ≫
        (modMultiSingle A M').inv := by
  apply eq_single_conj
  have s1 : modMultiπ A [M'] ≫ (ρ_ (modMulti A [M'])).inv =
      (ρ_ (modList A [M'])).inv ≫
        (modMultiπ A [M'] ▷ (𝟙_ D)) :=
    rightUnitor_inv_naturality _
  have s2 : (modMultiπ A [M'] ▷ (𝟙_ D)) ≫
      (modMulti A [M'] ◁ copairImage A c) =
    (modList A [M'] ◁ copairImage A c) ≫
      (modMultiπ A [M'] ▷ modMulti A [M, M']) :=
    (whisker_exchange _ _).symm
  have hbig : modMultiπ A [M'] ≫ zagComposite A c p hp ≫
      (modMultiSingle A M').hom =
    (ρ_ (modList A [M'])).inv ≫
      (modList A [M'] ◁ (η[A] ≫ c)) ≫
      ((modList A [M'] ◁ modMultiPairInv A M M') ≫
        (modMultiπ A [M'] ▷ modMulti A [M, M']) ≫
        modMultiConcat A [M'] [M, M'] ≫
        modMultiContract3L A p hp M' ≫
        (modMultiSingle A M').hom) := by
    simp only [zagComposite, Category.assoc]
    rw [reassoc_of% s1, reassoc_of% s2, copairImage_eq,
      MonoidalCategory.whiskerLeft_comp]
    repeat' erw [Category.assoc]
  have hcore := pairInv_concat_contract3L_single A p hp
  have hfin : (ρ_ (M'.X ⊗ 𝟙_ D)).inv ≫
      ((M'.X ⊗ 𝟙_ D) ◁ (η[A] ≫ c)) ≫
      (((ρ_ M'.X).hom ▷ modTensor A M M') ≫
        zagContract A p hp) =
    (ρ_ M'.X).hom ≫ (ρ_ M'.X).inv ≫
      (M'.X ◁ (η[A] ≫ c)) ≫ zagContract A p hp := by
    have s5 : ((M'.X ⊗ 𝟙_ D) ◁ (η[A] ≫ c)) ≫
        ((ρ_ M'.X).hom ▷ modTensor A M M') =
      ((ρ_ M'.X).hom ▷ (𝟙_ D)) ≫ (M'.X ◁ (η[A] ≫ c)) :=
      whisker_exchange _ _
    have s6 : (ρ_ (M'.X ⊗ 𝟙_ D)).inv ≫
        ((ρ_ M'.X).hom ▷ (𝟙_ D)) =
      (ρ_ M'.X).hom ≫ (ρ_ M'.X).inv := by
      monoidal
    rw [reassoc_of% s5, reassoc_of% s6]
  exact hbig.trans
    ((congrArg (fun t => (ρ_ (modList A [M'])).inv ≫
      (modList A [M'] ◁ (η[A] ≫ c)) ≫ t) hcore).trans hfin)

/-- The carrier zag identity from the multi-level zag law. -/
theorem zag_carrier_of_multi
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (h : zagComposite A c p hp = 𝟙 (modMulti A [M'])) :
    (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ c)) ≫
      zagContract A p hp = 𝟙 M'.X :=
  (iso_conj_id_iff (modMultiSingle A M')).mp
    ((zagComposite_eq_carrier A c p hp).symm.trans h)

/-- The multi-level zag law from the carrier zag identity. -/
theorem multi_of_zag_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M M')
    (p : modTensor A M' M ⟶ A)
    (hp : haveI := modTensorModObj A M' M
      actLeft A (modTensor A M' M) ≫ p = (A ◁ p) ≫ μ[A])
    (h : (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ c)) ≫
      zagContract A p hp = 𝟙 M'.X) :
    zagComposite A c p hp = 𝟙 (modMulti A [M']) := by
  rw [zagComposite_eq_carrier A c p hp, h, Category.id_comp,
    Iso.hom_inv_id]

end ZagCarrier

/-! ## The carrier identities of a zigzag datum -/

section Datum

/-- **The carrier zig identity of a zigzag datum**: insert the
copairing on the left of the carrier and contract; the composite
is the identity of `M.X`. -/
@[reassoc]
theorem zigzag_carrier_zig
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    {d : ModDualityDatum A M M'}
    (hz : ModZigzagDatum A d) :
    (λ_ M.X).inv ≫ ((η[A] ≫ d.copair) ▷ M.X) ≫
      zigContract A d.pair d.pair_linear = 𝟙 M.X :=
  zig_carrier_of_multi A d.copair d.pair d.pair_linear hz.zig

/-- **The carrier zag identity of a zigzag datum**: insert the
copairing on the right of the dual carrier and contract; the
composite is the identity of `M'.X`. -/
@[reassoc]
theorem zigzag_carrier_zag
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    {d : ModDualityDatum A M M'}
    (hz : ModZigzagDatum A d) :
    (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ d.copair)) ≫
      zagContract A d.pair d.pair_linear = 𝟙 M'.X :=
  zag_carrier_of_multi A d.copair d.pair d.pair_linear hz.zag

/-- **The converse packaging**: the multi-level zigzag laws from
the carrier-level triangle identities. -/
theorem modZigzagDatum_of_carrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    {d : ModDualityDatum A M M'}
    (hzig : (λ_ M.X).inv ≫ ((η[A] ≫ d.copair) ▷ M.X) ≫
      zigContract A d.pair d.pair_linear = 𝟙 M.X)
    (hzag : (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ d.copair)) ≫
      zagContract A d.pair d.pair_linear = 𝟙 M'.X) :
    ModZigzagDatum A d :=
  ⟨multi_of_zig_carrier A d.copair d.pair d.pair_linear hzig,
    multi_of_zag_carrier A d.copair d.pair d.pair_linear hzag⟩

end Datum

end RS
