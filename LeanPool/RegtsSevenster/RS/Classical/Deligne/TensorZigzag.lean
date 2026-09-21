/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MuInterchange
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZagAction
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagCarrier

/-!
# The tensor datum inherits the zigzag laws

Deligne's 1.15 tensor part, the verification "left to the
reader": the zigzag laws of two duality data pass to their
tensor.  The tensor copair element is the interchange of the two
copair elements, and the tensor contraction against a pure tensor
of carriers is the tensor of the component contractions; nesting
the two component triangles closes the tensor triangle.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The tensor copair element is the interchange of the copair
elements.** -/
theorem tensorCopair_point
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    η[A] ≫ tensorCopair A d₁ d₂ =
      (λ_ (𝟙_ D)).inv ≫
        ((η[A] ≫ d₁.copair) ⊗ₘ (η[A] ≫ d₂.copair)) ≫
        interchange A N₁ N₁' N₂ N₂' := by
  rw [tensorCopair]
  show η[A] ≫ regPairUnfold A ≫
      modTensorMap A d₁.copairMod d₂.copairMod ≫
      interchangeDesc A N₁ N₁' N₂ N₂' =
    (λ_ (𝟙_ D)).inv ≫
      ((η[A] ≫ d₁.copair) ⊗ₘ (η[A] ≫ d₂.copair)) ≫
      interchange A N₁ N₁' N₂ N₂'
  have hunfold : η[A] ≫ regPairUnfold A =
      (λ_ (𝟙_ D)).inv ≫ (η[A] ⊗ₘ η[A]) ≫
        modTensorπ A (regularMod A) (regularMod A) := by
    rw [regPairUnfold]
    show η[A] ≫ (λ_ A).inv ≫ η[A] ▷ A ≫
        modTensorπ A (regularMod A) (regularMod A) = _
    rw [leftUnitor_inv_naturality_assoc,
      whisker_exchange_assoc, MonoidalCategory.tensorHom_def,
      Category.assoc]
  have hmap : modTensorπ A (regularMod A) (regularMod A) ≫
      modTensorMap A d₁.copairMod d₂.copairMod =
      (d₁.copair ⊗ₘ d₂.copair) ≫
        modTensorπ A (modTensorMod A N₁ N₁')
          (modTensorMod A N₂ N₂') :=
    modTensorπ_map A d₁.copairMod d₂.copairMod
  have htail : modTensorπ A (regularMod A) (regularMod A) ≫
      modTensorMap A d₁.copairMod d₂.copairMod ≫
      interchangeDesc A N₁ N₁' N₂ N₂' =
      (d₁.copair ⊗ₘ d₂.copair) ≫
        interchange A N₁ N₁' N₂ N₂' := by
    rw [← Category.assoc, hmap, Category.assoc]
    exact congrArg (fun t : (modTensorMod A N₁ N₁').X ⊗
          (modTensorMod A N₂ N₂').X ⟶
          modTensor A (modTensorMod A N₁ N₂)
            (modTensorMod A N₁' N₂') =>
        (d₁.copair ⊗ₘ d₂.copair) ≫ t)
      (modTensorπ_interchangeDesc A N₁ N₁' N₂ N₂')
  rw [reassoc_of% hunfold, htail,
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]

/-- **Paired right actions descend to the joint action**: acting
on both carriers and projecting is multiplying the scalars and
acting on the projected pair — the quotient relation of the
relative tensor. -/
theorem tensorHom_actRight_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (N₁ N₂ : Mod D A) :
    (actRight A N₁.X ⊗ₘ actRight A N₂.X) ≫ modTensorπ A N₁ N₂ =
      tensorμ N₁.X A N₂.X A ≫
        ((N₁.X ⊗ N₂.X) ◁ μ[A]) ≫
        (modTensorπ A N₁ N₂ ▷ A) ≫
        (β_ (modTensor A N₁ N₂) A).hom ≫
        modTensorAct A N₁ N₂ := by
  have hR : (modTensorπ A N₁ N₂ ▷ A) ≫
      (β_ (modTensor A N₁ N₂) A).hom ≫
      modTensorAct A N₁ N₂ =
      (β_ (N₁.X ⊗ N₂.X) A).hom ≫
        (α_ A N₁.X N₂.X).inv ≫
        (actLeft A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ := by
    rw [BraidedCategory.braiding_naturality_left_assoc,
      whiskerLeft_modTensorπ_act]
    simp only [Category.assoc]
  have hcond : (actRight A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ =
      (α_ N₁.X A N₂.X).hom ≫
        (N₁.X ◁ actLeft A N₂.X) ≫ modTensorπ A N₁ N₂ := by
    have h := modTensor_condition A N₁ N₂
    rw [modTensorLegM, modTensorLegN] at h
    simpa using h
  have hcond' : (N₁.X ◁ actLeft A N₂.X) ≫ modTensorπ A N₁ N₂ =
      (α_ N₁.X A N₂.X).inv ≫
        (actRight A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ := by
    rw [hcond, Iso.inv_hom_id_assoc]
  have h2 : (N₁.X ◁ actRight A N₂.X) ≫ modTensorπ A N₁ N₂ =
      (N₁.X ◁ (β_ N₂.X A).hom) ≫ (α_ N₁.X A N₂.X).inv ≫
        (actRight A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ := by
    rw [actRight, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, hcond']
  have h3 : (actRight A N₁.X ▷ A ≫ actRight A N₁.X) ▷ N₂.X ≫
      modTensorπ A N₁ N₂ =
      ((α_ N₁.X A A).hom ▷ N₂.X) ≫
        ((N₁.X ◁ μ[A]) ▷ N₂.X) ≫
        (actRight A N₁.X ▷ N₂.X) ≫ modTensorπ A N₁ N₂ := by
    rw [actRight_actRight]
    simp only [comp_whiskerRight, Category.assoc]
  conv_lhs => rw [MonoidalCategory.tensorHom_def,
    Category.assoc, h2,
    ← whisker_exchange_assoc (actRight A N₁.X)
      ((β_ N₂.X A).hom),
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, h3]
  conv_lhs => rw [(show actRight A N₁.X =
      (β_ N₁.X A).hom ≫ actLeft A N₁.X from rfl),
    comp_whiskerRight, Category.assoc]
  conv_rhs => rw [hR]
  have hβμ : ((N₁.X ◁ μ[A]) ▷ N₂.X) ≫
      ((β_ N₁.X A).hom ▷ N₂.X) =
      ((β_ N₁.X (A ⊗ A)).hom ▷ N₂.X) ≫
        ((μ[A] ▷ N₁.X) ▷ N₂.X) := by
    rw [← comp_whiskerRight,
      BraidedCategory.braiding_naturality_right,
      comp_whiskerRight]
  have hβμ' : ((N₁.X ⊗ N₂.X) ◁ μ[A]) ≫
      (β_ (N₁.X ⊗ N₂.X) A).hom =
      (β_ (N₁.X ⊗ N₂.X) (A ⊗ A)).hom ≫
        (μ[A] ▷ (N₁.X ⊗ N₂.X)) := by
    rw [BraidedCategory.braiding_naturality_right]
  conv_lhs => rw [reassoc_of% hβμ]
  conv_rhs => rw [reassoc_of% hβμ',
    associator_inv_naturality_left_assoc]
  have hpre : ((N₁.X ⊗ A) ◁ (β_ N₂.X A).hom) ≫
      (α_ (N₁.X ⊗ A) A N₂.X).inv ≫
      ((α_ N₁.X A A).hom ▷ N₂.X) ≫
      ((β_ N₁.X (A ⊗ A)).hom ▷ N₂.X) =
      tensorμ N₁.X A N₂.X A ≫
        (β_ (N₁.X ⊗ N₂.X) (A ⊗ A)).hom ≫
        (α_ (A ⊗ A) N₁.X N₂.X).inv :=
    braid_prefix_coherence N₁.X A N₂.X
  rw [reassoc_of% hpre]

/-- **The tensor contraction against the interchange is the
tensor of the component contractions**: the crossing seats each
dual half against its own carrier. -/
theorem interchange_zigContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    ((modTensor A N₁ N₁' ⊗ modTensor A N₂ N₂') ◁
        modTensorπ A N₁ N₂) ≫
      (interchange A N₁ N₁' N₂ N₂' ▷ modTensor A N₁ N₂) ≫
      zigContract A (tensorDatum A d₁ d₂).pair
        (tensorDatum A d₁ d₂).pair_linear =
      tensorμ (modTensor A N₁ N₁') (modTensor A N₂ N₂')
          N₁.X N₂.X ≫
        (zigContract A d₁.pair d₁.pair_linear ⊗ₘ
          zigContract A d₂.pair d₂.pair_linear) ≫
        modTensorπ A N₁ N₂ := by
  refine (cancel_epi
    ((modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂') ▷
      (N₁.X ⊗ N₂.X))).mp ?_
  have hpair : (tensorDatum A d₁ d₂).pair =
      interchangeDesc A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A := rfl
  have hinner : modTensorπ A (modTensorMod A N₁' N₂')
      (modTensorMod A N₁ N₂) ≫ (tensorDatum A d₁ d₂).pair =
      interchange A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A := by
    rw [hpair, ← Category.assoc, modTensorπ_interchangeDesc]
    rfl
  conv_lhs => rw [← whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, tensorHom_π_interchange,
    rawInterchangeπ, rawInterchange]
  have hzdef : (MonoidalCategory.whiskerRight
      (X₁ := modTensor A N₁ N₂ ⊗ modTensor A N₁' N₂')
      (modTensorπ A (modTensorMod A N₁ N₂)
        (modTensorMod A N₁' N₂'))
      (modTensor A N₁ N₂)) ≫
      zigContract A (tensorDatum A d₁ d₂).pair
        (tensorDatum A d₁ d₂).pair_linear =
      (α_ (modTensorMod A N₁ N₂).X (modTensorMod A N₁' N₂').X
        (modTensorMod A N₁ N₂).X).hom ≫
      ((modTensorMod A N₁ N₂).X ◁
        (modTensorπ A (modTensorMod A N₁' N₂')
          (modTensorMod A N₁ N₂) ≫
          (tensorDatum A d₁ d₂).pair)) ≫
      actRight A (modTensorMod A N₁ N₂).X :=
    whiskerRight_modTensorπ_zigContract A
      (tensorDatum A d₁ d₂).pair
      (tensorDatum A d₁ d₂).pair_linear
  conv_lhs => rw [comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc, hzdef]
  -- The inner contraction word, fully reduced at the fold.
  have hfold : modTensorπ A (regularMod A) (regularMod A) ≫
      regPairFold A = μ[A] := by
    rw [regPairFold]
    exact modTensorπ_desc A _ _ _ _
  have hw : ((modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂) :
        (N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X) ⟶ _) ≫
      interchange A N₁' N₂' N₁ N₂ ≫
      modTensorMap A d₁.pairMod d₂.pairMod ≫ regPairFold A =
      tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A] := by
    have hm : modTensorπ A (modTensorMod A N₁' N₁)
        (modTensorMod A N₂' N₂) ≫
        modTensorMap A d₁.pairMod d₂.pairMod =
        (d₁.pair ⊗ₘ d₂.pair) ≫
          modTensorπ A (regularMod A) (regularMod A) :=
      modTensorπ_map A d₁.pairMod d₂.pairMod
    have htail : (modTensorπ A N₁' N₁ ⊗ₘ modTensorπ A N₂' N₂) ≫
        modTensorπ A (modTensorMod A N₁' N₁)
          (modTensorMod A N₂' N₂) ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A =
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A] := by
      have t2 : modTensorπ A (modTensorMod A N₁' N₁)
          (modTensorMod A N₂' N₂) ≫
          modTensorMap A d₁.pairMod d₂.pairMod ≫
          regPairFold A =
          (d₁.pair ⊗ₘ d₂.pair) ≫ μ[A] := by
        rw [← Category.assoc, hm]
        exact (Category.assoc _ _ _).trans
          (congrArg (fun t : (regularMod A).X ⊗
              (regularMod A).X ⟶ A =>
            (d₁.pair ⊗ₘ d₂.pair) ≫ t) hfold)
      exact (congrArg (fun t : (modTensorMod A N₁' N₁).X ⊗
            (modTensorMod A N₂' N₂).X ⟶ A =>
          (modTensorπ A N₁' N₁ ⊗ₘ modTensorπ A N₂' N₂) ≫ t)
        t2).trans (by
          rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc])
    rw [← Category.assoc, tensorHom_π_interchange,
      rawInterchangeπ, rawInterchange, Category.assoc,
      Category.assoc]
    exact congrArg (fun t : (N₁'.X ⊗ N₁.X) ⊗ (N₂'.X ⊗ N₂.X) ⟶
        A => tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫ t) htail
  conv_lhs => rw [hinner]
  conv_lhs => rw [whisker_exchange_assoc
      (tensorμ N₁.X N₁'.X N₂.X N₂'.X) (modTensorπ A N₁ N₂),
    whisker_exchange_assoc
      (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂')
      (modTensorπ A N₁ N₂)]
  conv_lhs => rw [← reassoc_of% (MonoidalCategory.tensorHom_def
      (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂')
      (modTensorπ A N₁ N₂))]
  have hα : ((modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂') ⊗ₘ
      modTensorπ A N₁ N₂) ≫
      (α_ (modTensor A N₁ N₂) (modTensor A N₁' N₂')
        (modTensor A N₁ N₂)).hom =
      (α_ (N₁.X ⊗ N₂.X) (N₁'.X ⊗ N₂'.X) (N₁.X ⊗ N₂.X)).hom ≫
        (modTensorπ A N₁ N₂ ⊗ₘ
          (modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂)) :=
    associator_naturality (modTensorπ A N₁ N₂)
      (modTensorπ A N₁' N₂') (modTensorπ A N₁ N₂)
  have hbig : (modTensorπ A N₁ N₂ ⊗ₘ
      (modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂)) ≫
      (modTensor A N₁ N₂ ◁
        (interchange A N₁' N₂' N₁ N₂ ≫
          modTensorMap A d₁.pairMod d₂.pairMod ≫
          regPairFold A)) =
      modTensorπ A N₁ N₂ ⊗ₘ
        (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
          ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
            (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]
    exact congrArg (fun t : (N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X) ⟶
        A => modTensorπ A N₁ N₂ ⊗ₘ t) hw
  have hslot : (modTensorπ A N₁ N₂ ⊗ₘ
      (modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂)) ≫
      ((modTensor A N₁ N₂ ◁
        (interchange A N₁' N₂' N₁ N₂ ≫
          modTensorMap A d₁.pairMod d₂.pairMod ≫
          regPairFold A)) ≫
        actRight A (modTensorMod A N₁ N₂).X) =
      (modTensorπ A N₁ N₂ ⊗ₘ
        (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
          ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
            (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A])) ≫
        actRight A (modTensorMod A N₁ N₂).X :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t : (N₁.X ⊗ N₂.X) ⊗
          ((N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X)) ⟶
          modTensor A N₁ N₂ ⊗ A =>
        t ≫ actRight A (modTensorMod A N₁ N₂).X) hbig)
  have hstep : ((modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂') ⊗ₘ
      modTensorπ A N₁ N₂) ≫
      ((α_ (modTensor A N₁ N₂) (modTensor A N₁' N₂')
        (modTensor A N₁ N₂)).hom ≫
      ((modTensor A N₁ N₂ ◁
        (interchange A N₁' N₂' N₁ N₂ ≫
          modTensorMap A d₁.pairMod d₂.pairMod ≫
          regPairFold A)) ≫
        actRight A (modTensorMod A N₁ N₂).X)) =
      (α_ (N₁.X ⊗ N₂.X) (N₁'.X ⊗ N₂'.X) (N₁.X ⊗ N₂.X)).hom ≫
        ((modTensorπ A N₁ N₂ ⊗ₘ
          (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
            ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
              (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A])) ≫
          actRight A (modTensorMod A N₁ N₂).X) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun t : ((N₁.X ⊗ N₂.X) ⊗ (N₁'.X ⊗ N₂'.X)) ⊗
            (N₁.X ⊗ N₂.X) ⟶
            modTensor A N₁ N₂ ⊗
              (modTensor A N₁' N₂' ⊗ modTensor A N₁ N₂) =>
          t ≫ ((modTensor A N₁ N₂ ◁
            (interchange A N₁' N₂' N₁ N₂ ≫
              modTensorMap A d₁.pairMod d₂.pairMod ≫
              regPairFold A)) ≫
            actRight A (modTensorMod A N₁ N₂).X)) hα).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : (N₁.X ⊗ N₂.X) ⊗
          ((N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X)) ⟶
          modTensor A N₁ N₂ =>
        (α_ (N₁.X ⊗ N₂.X) (N₁'.X ⊗ N₂'.X)
          (N₁.X ⊗ N₂.X)).hom ≫ t) hslot
  refine Eq.trans (congrArg (fun s : ((N₁.X ⊗ N₂.X) ⊗
        (N₁'.X ⊗ N₂'.X)) ⊗ (N₁.X ⊗ N₂.X) ⟶
        modTensor A N₁ N₂ =>
      tensorμ N₁.X N₁'.X N₂.X N₂'.X ▷ (N₁.X ⊗ N₂.X) ≫ s)
    hstep) ?_
  have hL : (modTensorπ A N₁ N₂ ⊗ₘ
      (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A])) ≫
      actRight A (modTensorMod A N₁ N₂).X =
      ((N₁.X ⊗ N₂.X) ◁
        (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
          ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
            (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A])) ≫
      (β_ (N₁.X ⊗ N₂.X) A).hom ≫
      (A ◁ modTensorπ A N₁ N₂) ≫ modTensorAct A N₁ N₂ := by
    show (modTensorπ A N₁ N₂ ⊗ₘ
        (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
          ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
            (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A])) ≫
        (β_ (modTensor A N₁ N₂) A).hom ≫
        modTensorAct A N₁ N₂ = _
    rw [← Category.assoc,
      BraidedCategory.braiding_naturality, Category.assoc,
      MonoidalCategory.tensorHom_def, ← Category.assoc,
      ← Category.assoc,
      ← BraidedCategory.braiding_naturality_right]
    simp only [Category.assoc]
  refine Eq.trans (congrArg (fun t : (N₁.X ⊗ N₂.X) ⊗
        ((N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X)) ⟶
        modTensor A N₁ N₂ =>
      tensorμ N₁.X N₁'.X N₂.X N₂'.X ▷ (N₁.X ⊗ N₂.X) ≫
        ((α_ (N₁.X ⊗ N₂.X) (N₁'.X ⊗ N₂'.X)
          (N₁.X ⊗ N₂.X)).hom ≫ t)) hL) ?_
  have hμnat : ((modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂') ▷
      (N₁.X ⊗ N₂.X)) ≫
      tensorμ (modTensor A N₁ N₁') (modTensor A N₂ N₂')
        N₁.X N₂.X =
      tensorμ (N₁.X ⊗ N₁'.X) (N₂.X ⊗ N₂'.X) N₁.X N₂.X ≫
        ((modTensorπ A N₁ N₁' ▷ N₁.X) ⊗ₘ
          (modTensorπ A N₂ N₂' ▷ N₂.X)) := by
    simpa using tensorμ_natural (modTensorπ A N₁ N₁')
      (modTensorπ A N₂ N₂') (𝟙 N₁.X) (𝟙 N₂.X)
  have hzc₁ : (modTensorπ A N₁ N₁' ▷ N₁.X) ≫
      zigContract A d₁.pair d₁.pair_linear =
      (α_ N₁.X N₁'.X N₁.X).hom ≫
        (N₁.X ◁ (modTensorπ A N₁' N₁ ≫ d₁.pair)) ≫
        actRight A N₁.X :=
    whiskerRight_modTensorπ_zigContract A d₁.pair
      d₁.pair_linear
  have hzc₂ : (modTensorπ A N₂ N₂' ▷ N₂.X) ≫
      zigContract A d₂.pair d₂.pair_linear =
      (α_ N₂.X N₂'.X N₂.X).hom ≫
        (N₂.X ◁ (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫
        actRight A N₂.X :=
    whiskerRight_modTensorπ_zigContract A d₂.pair
      d₂.pair_linear
  have hpair2 : ((modTensorπ A N₁ N₁' ▷ N₁.X) ⊗ₘ
      (modTensorπ A N₂ N₂' ▷ N₂.X)) ≫
      (zigContract A d₁.pair d₁.pair_linear ⊗ₘ
        zigContract A d₂.pair d₂.pair_linear) =
      ((α_ N₁.X N₁'.X N₁.X).hom ⊗ₘ
        (α_ N₂.X N₂'.X N₂.X).hom) ≫
        ((N₁.X ◁ (modTensorπ A N₁' N₁ ≫ d₁.pair)) ⊗ₘ
          (N₂.X ◁ (modTensorπ A N₂' N₂ ≫ d₂.pair))) ≫
        (actRight A N₁.X ⊗ₘ actRight A N₂.X) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, hzc₁, hzc₂,
      ← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
  have hR : ((modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂') ▷
      (N₁.X ⊗ N₂.X)) ≫
      (tensorμ (modTensor A N₁ N₁') (modTensor A N₂ N₂')
        N₁.X N₂.X ≫
      ((zigContract A d₁.pair d₁.pair_linear ⊗ₘ
        zigContract A d₂.pair d₂.pair_linear) ≫
        modTensorπ A N₁ N₂)) =
      tensorμ (N₁.X ⊗ N₁'.X) (N₂.X ⊗ N₂'.X) N₁.X N₂.X ≫
        (((α_ N₁.X N₁'.X N₁.X).hom ⊗ₘ
          (α_ N₂.X N₂'.X N₂.X).hom) ≫
        (((N₁.X ◁ (modTensorπ A N₁' N₁ ≫ d₁.pair)) ⊗ₘ
          (N₂.X ◁ (modTensorπ A N₂' N₂ ≫ d₂.pair))) ≫
        (tensorμ N₁.X A N₂.X A ≫
          ((N₁.X ⊗ N₂.X) ◁ μ[A]) ≫
          (modTensorπ A N₁ N₂ ▷ A) ≫
          (β_ (modTensor A N₁ N₂) A).hom ≫
          modTensorAct A N₁ N₂))) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun t : (((N₁.X ⊗ N₁'.X) ⊗ (N₂.X ⊗ N₂'.X)) ⊗
            (N₁.X ⊗ N₂.X)) ⟶
            ((modTensor A N₁ N₁' ⊗ N₁.X) ⊗
              (modTensor A N₂ N₂' ⊗ N₂.X)) =>
          t ≫ ((zigContract A d₁.pair d₁.pair_linear ⊗ₘ
            zigContract A d₂.pair d₂.pair_linear) ≫
            modTensorπ A N₁ N₂)) hμnat).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : ((N₁.X ⊗ N₁'.X) ⊗ N₁.X) ⊗
            ((N₂.X ⊗ N₂'.X) ⊗ N₂.X) ⟶ modTensor A N₁ N₂ =>
        tensorμ (N₁.X ⊗ N₁'.X) (N₂.X ⊗ N₂'.X) N₁.X N₂.X ≫ t) <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun t : ((N₁.X ⊗ N₁'.X) ⊗ N₁.X) ⊗
            ((N₂.X ⊗ N₂'.X) ⊗ N₂.X) ⟶ N₁.X ⊗ N₂.X =>
        t ≫ modTensorπ A N₁ N₂) hpair2).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : (N₁.X ⊗ (N₁'.X ⊗ N₁.X)) ⊗
            (N₂.X ⊗ (N₂'.X ⊗ N₂.X)) ⟶ modTensor A N₁ N₂ =>
        ((α_ N₁.X N₁'.X N₁.X).hom ⊗ₘ
          (α_ N₂.X N₂'.X N₂.X).hom) ≫ t) <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : (N₁.X ⊗ A) ⊗ (N₂.X ⊗ A) ⟶
            modTensor A N₁ N₂ =>
        ((N₁.X ◁ (modTensorπ A N₁' N₁ ≫ d₁.pair)) ⊗ₘ
          (N₂.X ◁ (modTensorπ A N₂' N₂ ≫ d₂.pair))) ≫ t)
        (tensorHom_actRight_π A N₁ N₂)
  refine Eq.trans ?_ hR.symm
  conv_lhs => rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  conv_lhs => rw [reassoc_of% (tensorMu_assoc_swap
      N₁.X N₁'.X N₂.X N₂'.X N₁.X N₂.X)]
  have hμnat₂ : ((N₁.X ◁ (modTensorπ A N₁' N₁ ≫ d₁.pair)) ⊗ₘ
      (N₂.X ◁ (modTensorπ A N₂' N₂ ≫ d₂.pair))) ≫
      tensorμ N₁.X A N₂.X A =
      tensorμ N₁.X (N₁'.X ⊗ N₁.X) N₂.X (N₂'.X ⊗ N₂.X) ≫
        ((N₁.X ⊗ N₂.X) ◁
          ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
            (modTensorπ A N₂' N₂ ≫ d₂.pair))) := by
    simpa using tensorμ_natural (𝟙 N₁.X)
      (modTensorπ A N₁' N₁ ≫ d₁.pair) (𝟙 N₂.X)
      (modTensorπ A N₂' N₂ ≫ d₂.pair)
  have hβl : (modTensorπ A N₁ N₂ ▷ A) ≫
      (β_ (modTensor A N₁ N₂) A).hom =
      (β_ (N₁.X ⊗ N₂.X) A).hom ≫ (A ◁ modTensorπ A N₁ N₂) :=
    BraidedCategory.braiding_naturality_left
      (modTensorπ A N₁ N₂) A
  conv_rhs => rw [reassoc_of% hμnat₂, reassoc_of% hβl]

/-- **The tensor contraction against the interchange is the
tensor of the component contractions**, zag side: the crossing
seats each dual half against its own carrier. -/
theorem interchange_zagContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    (modTensorπ A N₁' N₂' ▷
        (modTensor A N₁ N₁' ⊗ modTensor A N₂ N₂')) ≫
      (modTensor A N₁' N₂' ◁ interchange A N₁ N₁' N₂ N₂') ≫
      zagContract A (tensorDatum A d₁ d₂).pair
        (tensorDatum A d₁ d₂).pair_linear =
      tensorμ N₁'.X N₂'.X (modTensor A N₁ N₁')
          (modTensor A N₂ N₂') ≫
        (zagContract A d₁.pair d₁.pair_linear ⊗ₘ
          zagContract A d₂.pair d₂.pair_linear) ≫
        modTensorπ A N₁' N₂' := by
  refine (cancel_epi
    ((N₁'.X ⊗ N₂'.X) ◁
      (modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂'))).mp ?_
  have hpair : (tensorDatum A d₁ d₂).pair =
      interchangeDesc A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A := rfl
  have hinner : modTensorπ A (modTensorMod A N₁' N₂')
      (modTensorMod A N₁ N₂) ≫ (tensorDatum A d₁ d₂).pair =
      interchange A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A := by
    rw [hpair, ← Category.assoc, modTensorπ_interchangeDesc]
    rfl
  conv_lhs => rw [whisker_exchange_assoc
      (modTensorπ A N₁' N₂')
      (modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂'),
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    tensorHom_π_interchange, rawInterchangeπ, rawInterchange]
  have hzagdef : (MonoidalCategory.whiskerLeft
      (modTensor A N₁' N₂')
      (modTensorπ A (modTensorMod A N₁ N₂)
        (modTensorMod A N₁' N₂'))) ≫
      zagContract A (tensorDatum A d₁ d₂).pair
        (tensorDatum A d₁ d₂).pair_linear =
      (α_ (modTensorMod A N₁' N₂').X (modTensorMod A N₁ N₂).X
        (modTensorMod A N₁' N₂').X).inv ≫
      ((modTensorπ A (modTensorMod A N₁' N₂')
          (modTensorMod A N₁ N₂) ≫
        (tensorDatum A d₁ d₂).pair) ▷
        (modTensorMod A N₁' N₂').X) ≫
      actLeft A (modTensorMod A N₁' N₂').X :=
    whiskerLeft_modTensorπ_zagContract A
      (tensorDatum A d₁ d₂).pair
      (tensorDatum A d₁ d₂).pair_linear
  conv_lhs => rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Category.assoc]
  refine Eq.trans (congrArg
    (fun t : modTensor A N₁' N₂' ⊗
        (modTensor A N₁ N₂ ⊗ modTensor A N₁' N₂') ⟶
        modTensor A N₁' N₂' =>
      (modTensorπ A N₁' N₂' ▷
          ((N₁.X ⊗ N₁'.X) ⊗ (N₂.X ⊗ N₂'.X))) ≫
        ((modTensor A N₁' N₂' ◁
          tensorμ N₁.X N₁'.X N₂.X N₂'.X) ≫
        ((modTensor A N₁' N₂' ◁
          (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂')) ≫
          t))) hzagdef) ?_
  conv_lhs => rw [hinner]
  conv_lhs => rw [← whisker_exchange_assoc
      (modTensorπ A N₁' N₂')
      (tensorμ N₁.X N₁'.X N₂.X N₂'.X),
    ← whisker_exchange_assoc (modTensorπ A N₁' N₂')
      (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂')]
  -- The inner contraction word, fully reduced at the fold.
  have hfold : modTensorπ A (regularMod A) (regularMod A) ≫
      regPairFold A = μ[A] := by
    rw [regPairFold]
    exact modTensorπ_desc A _ _ _ _
  have hw : ((modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂) :
        (N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X) ⟶ _) ≫
      interchange A N₁' N₂' N₁ N₂ ≫
      modTensorMap A d₁.pairMod d₂.pairMod ≫ regPairFold A =
      tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A] := by
    have hm : modTensorπ A (modTensorMod A N₁' N₁)
        (modTensorMod A N₂' N₂) ≫
        modTensorMap A d₁.pairMod d₂.pairMod =
        (d₁.pair ⊗ₘ d₂.pair) ≫
          modTensorπ A (regularMod A) (regularMod A) :=
      modTensorπ_map A d₁.pairMod d₂.pairMod
    have htail : (modTensorπ A N₁' N₁ ⊗ₘ modTensorπ A N₂' N₂) ≫
        modTensorπ A (modTensorMod A N₁' N₁)
          (modTensorMod A N₂' N₂) ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A =
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A] := by
      have t2 : modTensorπ A (modTensorMod A N₁' N₁)
          (modTensorMod A N₂' N₂) ≫
          modTensorMap A d₁.pairMod d₂.pairMod ≫
          regPairFold A =
          (d₁.pair ⊗ₘ d₂.pair) ≫ μ[A] := by
        rw [← Category.assoc, hm]
        exact (Category.assoc _ _ _).trans
          (congrArg (fun t : (regularMod A).X ⊗
              (regularMod A).X ⟶ A =>
            (d₁.pair ⊗ₘ d₂.pair) ≫ t) hfold)
      exact (congrArg (fun t : (modTensorMod A N₁' N₁).X ⊗
            (modTensorMod A N₂' N₂).X ⟶ A =>
          (modTensorπ A N₁' N₁ ⊗ₘ modTensorπ A N₂' N₂) ≫ t)
        t2).trans (by
          rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc])
    rw [← Category.assoc, tensorHom_π_interchange,
      rawInterchangeπ, rawInterchange, Category.assoc,
      Category.assoc]
    exact congrArg (fun t : (N₁'.X ⊗ N₁.X) ⊗ (N₂'.X ⊗ N₂.X) ⟶
        A => tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫ t) htail
  conv_lhs => rw [← reassoc_of% (MonoidalCategory.tensorHom_def'
      (modTensorπ A N₁' N₂')
      (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂'))]
  have hα : (modTensorπ A N₁' N₂' ⊗ₘ
      (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂')) ≫
      (α_ (modTensor A N₁' N₂') (modTensor A N₁ N₂)
        (modTensor A N₁' N₂')).inv =
      (α_ (N₁'.X ⊗ N₂'.X) (N₁.X ⊗ N₂.X)
        (N₁'.X ⊗ N₂'.X)).inv ≫
        ((modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂) ⊗ₘ
          modTensorπ A N₁' N₂') :=
    associator_inv_naturality (modTensorπ A N₁' N₂')
      (modTensorπ A N₁ N₂) (modTensorπ A N₁' N₂')
  have hbig : ((modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂) ⊗ₘ
      modTensorπ A N₁' N₂') ≫
      ((interchange A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A) ▷ modTensor A N₁' N₂') =
      (tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) ⊗ₘ
        modTensorπ A N₁' N₂' := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]
    exact congrArg (fun t : (N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X) ⟶
        A => t ⊗ₘ modTensorπ A N₁' N₂') hw
  have hslot : ((modTensorπ A N₁' N₂' ⊗ₘ modTensorπ A N₁ N₂) ⊗ₘ
      modTensorπ A N₁' N₂') ≫
      (((interchange A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A) ▷ modTensor A N₁' N₂') ≫
        actLeft A (modTensorMod A N₁' N₂').X) =
      ((tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) ⊗ₘ
        modTensorπ A N₁' N₂') ≫
        actLeft A (modTensorMod A N₁' N₂').X :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t : ((N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X)) ⊗
          (N₁'.X ⊗ N₂'.X) ⟶ A ⊗ modTensor A N₁' N₂' =>
        t ≫ actLeft A (modTensorMod A N₁' N₂').X) hbig)
  have hstep : (modTensorπ A N₁' N₂' ⊗ₘ
      (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A N₁' N₂')) ≫
      ((α_ (modTensor A N₁' N₂') (modTensor A N₁ N₂)
        (modTensor A N₁' N₂')).inv ≫
      (((interchange A N₁' N₂' N₁ N₂ ≫
        modTensorMap A d₁.pairMod d₂.pairMod ≫
        regPairFold A) ▷ modTensor A N₁' N₂') ≫
        actLeft A (modTensorMod A N₁' N₂').X)) =
      (α_ (N₁'.X ⊗ N₂'.X) (N₁.X ⊗ N₂.X)
        (N₁'.X ⊗ N₂'.X)).inv ≫
        (((tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
          ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
            (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) ⊗ₘ
          modTensorπ A N₁' N₂') ≫
          actLeft A (modTensorMod A N₁' N₂').X) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun t : ((N₁'.X ⊗ N₂'.X) ⊗
            ((N₁.X ⊗ N₂.X) ⊗ (N₁'.X ⊗ N₂'.X))) ⟶
            (modTensor A N₁' N₂' ⊗ modTensor A N₁ N₂) ⊗
              modTensor A N₁' N₂' =>
          t ≫ (((interchange A N₁' N₂' N₁ N₂ ≫
            modTensorMap A d₁.pairMod d₂.pairMod ≫
            regPairFold A) ▷ modTensor A N₁' N₂') ≫
            actLeft A (modTensorMod A N₁' N₂').X)) hα).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : ((N₁'.X ⊗ N₂'.X) ⊗ (N₁.X ⊗ N₂.X)) ⊗
            (N₁'.X ⊗ N₂'.X) ⟶ modTensor A N₁' N₂' =>
        (α_ (N₁'.X ⊗ N₂'.X) (N₁.X ⊗ N₂.X)
          (N₁'.X ⊗ N₂'.X)).inv ≫ t) hslot
  refine Eq.trans (congrArg (fun s : (N₁'.X ⊗ N₂'.X) ⊗
        ((N₁.X ⊗ N₂.X) ⊗ (N₁'.X ⊗ N₂'.X)) ⟶
        modTensor A N₁' N₂' =>
      ((N₁'.X ⊗ N₂'.X) ◁ tensorμ N₁.X N₁'.X N₂.X N₂'.X) ≫ s)
    hstep) ?_
  have hL : ((tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
      ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
        (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) ⊗ₘ
      modTensorπ A N₁' N₂') ≫
      actLeft A (modTensorMod A N₁' N₂').X =
      ((tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) ▷
        (N₁'.X ⊗ N₂'.X)) ≫
      (A ◁ modTensorπ A N₁' N₂') ≫
      modTensorAct A N₁' N₂' := by
    show ((tensorμ N₁'.X N₂'.X N₁.X N₂.X ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ≫ μ[A]) ⊗ₘ
        modTensorπ A N₁' N₂') ≫
        modTensorAct A N₁' N₂' = _
    rw [MonoidalCategory.tensorHom_def, Category.assoc]
  refine Eq.trans (congrArg (fun t : ((N₁'.X ⊗ N₂'.X) ⊗
        (N₁.X ⊗ N₂.X)) ⊗ (N₁'.X ⊗ N₂'.X) ⟶
        modTensor A N₁' N₂' =>
      ((N₁'.X ⊗ N₂'.X) ◁ tensorμ N₁.X N₁'.X N₂.X N₂'.X) ≫
        ((α_ (N₁'.X ⊗ N₂'.X) (N₁.X ⊗ N₂.X)
          (N₁'.X ⊗ N₂'.X)).inv ≫ t)) hL) ?_
  have hμnat : ((N₁'.X ⊗ N₂'.X) ◁
      (modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂')) ≫
      tensorμ N₁'.X N₂'.X (modTensor A N₁ N₁')
        (modTensor A N₂ N₂') =
      tensorμ N₁'.X N₂'.X (N₁.X ⊗ N₁'.X) (N₂.X ⊗ N₂'.X) ≫
        ((N₁'.X ◁ modTensorπ A N₁ N₁') ⊗ₘ
          (N₂'.X ◁ modTensorπ A N₂ N₂')) := by
    simpa using tensorμ_natural (𝟙 N₁'.X) (𝟙 N₂'.X)
      (modTensorπ A N₁ N₁') (modTensorπ A N₂ N₂')
  have hzagc₁ : (N₁'.X ◁ modTensorπ A N₁ N₁') ≫
      zagContract A d₁.pair d₁.pair_linear =
      (α_ N₁'.X N₁.X N₁'.X).inv ≫
        ((modTensorπ A N₁' N₁ ≫ d₁.pair) ▷ N₁'.X) ≫
        actLeft A N₁'.X :=
    whiskerLeft_modTensorπ_zagContract A d₁.pair
      d₁.pair_linear
  have hzagc₂ : (N₂'.X ◁ modTensorπ A N₂ N₂') ≫
      zagContract A d₂.pair d₂.pair_linear =
      (α_ N₂'.X N₂.X N₂'.X).inv ≫
        ((modTensorπ A N₂' N₂ ≫ d₂.pair) ▷ N₂'.X) ≫
        actLeft A N₂'.X :=
    whiskerLeft_modTensorπ_zagContract A d₂.pair
      d₂.pair_linear
  have hpair2 : ((N₁'.X ◁ modTensorπ A N₁ N₁') ⊗ₘ
      (N₂'.X ◁ modTensorπ A N₂ N₂')) ≫
      (zagContract A d₁.pair d₁.pair_linear ⊗ₘ
        zagContract A d₂.pair d₂.pair_linear) =
      ((α_ N₁'.X N₁.X N₁'.X).inv ⊗ₘ
        (α_ N₂'.X N₂.X N₂'.X).inv) ≫
        (((modTensorπ A N₁' N₁ ≫ d₁.pair) ▷ N₁'.X) ⊗ₘ
          ((modTensorπ A N₂' N₂ ≫ d₂.pair) ▷ N₂'.X)) ≫
        (actLeft A N₁'.X ⊗ₘ actLeft A N₂'.X) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      hzagc₁, hzagc₂,
      ← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
  have hR : ((N₁'.X ⊗ N₂'.X) ◁
      (modTensorπ A N₁ N₁' ⊗ₘ modTensorπ A N₂ N₂')) ≫
      (tensorμ N₁'.X N₂'.X (modTensor A N₁ N₁')
        (modTensor A N₂ N₂') ≫
      ((zagContract A d₁.pair d₁.pair_linear ⊗ₘ
        zagContract A d₂.pair d₂.pair_linear) ≫
        modTensorπ A N₁' N₂')) =
      tensorμ N₁'.X N₂'.X (N₁.X ⊗ N₁'.X) (N₂.X ⊗ N₂'.X) ≫
        (((α_ N₁'.X N₁.X N₁'.X).inv ⊗ₘ
          (α_ N₂'.X N₂.X N₂'.X).inv) ≫
        ((((modTensorπ A N₁' N₁ ≫ d₁.pair) ▷ N₁'.X) ⊗ₘ
          ((modTensorπ A N₂' N₂ ≫ d₂.pair) ▷ N₂'.X)) ≫
        (tensorμ A N₁'.X A N₂'.X ≫
          (μ[A] ▷ (N₁'.X ⊗ N₂'.X)) ≫
          (A ◁ modTensorπ A N₁' N₂') ≫
          modTensorAct A N₁' N₂'))) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun t : ((N₁'.X ⊗ N₂'.X) ⊗
            ((N₁.X ⊗ N₁'.X) ⊗ (N₂.X ⊗ N₂'.X))) ⟶
            ((N₁'.X ⊗ modTensor A N₁ N₁') ⊗
              (N₂'.X ⊗ modTensor A N₂ N₂')) =>
          t ≫ ((zagContract A d₁.pair d₁.pair_linear ⊗ₘ
            zagContract A d₂.pair d₂.pair_linear) ≫
            modTensorπ A N₁' N₂')) hμnat).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : (N₁'.X ⊗ (N₁.X ⊗ N₁'.X)) ⊗
            (N₂'.X ⊗ (N₂.X ⊗ N₂'.X)) ⟶ modTensor A N₁' N₂' =>
        tensorμ N₁'.X N₂'.X (N₁.X ⊗ N₁'.X)
          (N₂.X ⊗ N₂'.X) ≫ t) <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun t : (N₁'.X ⊗ (N₁.X ⊗ N₁'.X)) ⊗
            (N₂'.X ⊗ (N₂.X ⊗ N₂'.X)) ⟶ N₁'.X ⊗ N₂'.X =>
        t ≫ modTensorπ A N₁' N₂') hpair2).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : ((N₁'.X ⊗ N₁.X) ⊗ N₁'.X) ⊗
            ((N₂'.X ⊗ N₂.X) ⊗ N₂'.X) ⟶ modTensor A N₁' N₂' =>
        ((α_ N₁'.X N₁.X N₁'.X).inv ⊗ₘ
          (α_ N₂'.X N₂.X N₂'.X).inv) ≫ t) <|
      (Category.assoc _ _ _).trans <|
      congrArg (fun t : (A ⊗ N₁'.X) ⊗ (A ⊗ N₂'.X) ⟶
            modTensor A N₁' N₂' =>
        (((modTensorπ A N₁' N₁ ≫ d₁.pair) ▷ N₁'.X) ⊗ₘ
          ((modTensorπ A N₂' N₂ ≫ d₂.pair) ▷ N₂'.X)) ≫ t)
        (tensorHom_actLeft_π A N₁' N₂')
  refine Eq.trans ?_ hR.symm
  conv_lhs => rw [comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  conv_lhs => rw [reassoc_of% (tensorMu_assoc_swap_inv
      N₁'.X N₂'.X N₁.X N₁'.X N₂.X N₂'.X)]
  have hμnat₂ : (((modTensorπ A N₁' N₁ ≫ d₁.pair) ▷ N₁'.X) ⊗ₘ
      ((modTensorπ A N₂' N₂ ≫ d₂.pair) ▷ N₂'.X)) ≫
      tensorμ A N₁'.X A N₂'.X =
      tensorμ (N₁'.X ⊗ N₁.X) N₁'.X (N₂'.X ⊗ N₂.X) N₂'.X ≫
        (((modTensorπ A N₁' N₁ ≫ d₁.pair) ⊗ₘ
          (modTensorπ A N₂' N₂ ≫ d₂.pair)) ▷
          (N₁'.X ⊗ N₂'.X)) := by
    simpa using tensorμ_natural
      (modTensorπ A N₁' N₁ ≫ d₁.pair) (𝟙 N₁'.X)
      (modTensorπ A N₂' N₂ ≫ d₂.pair) (𝟙 N₂'.X)
  conv_rhs => rw [reassoc_of% hμnat₂]

/-- **The tensor datum inherits the carrier zig identity.** -/
theorem tensorDatum_carrier_zig
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂')
    (hz₁ : (λ_ N₁.X).inv ≫ ((η[A] ≫ d₁.copair) ▷ N₁.X) ≫
      zigContract A d₁.pair d₁.pair_linear = 𝟙 N₁.X)
    (hz₂ : (λ_ N₂.X).inv ≫ ((η[A] ≫ d₂.copair) ▷ N₂.X) ≫
      zigContract A d₂.pair d₂.pair_linear = 𝟙 N₂.X) :
    (λ_ (modTensor A N₁ N₂)).inv ≫
      ((η[A] ≫ (tensorDatum A d₁ d₂).copair) ▷
        modTensor A N₁ N₂) ≫
      zigContract A (tensorDatum A d₁ d₂).pair
        (tensorDatum A d₁ d₂).pair_linear =
      𝟙 (modTensor A N₁ N₂) := by
  have hpt₁ : (η[A] ≫ d₁.copair) ▷ N₁.X ≫
      zigContract A d₁.pair d₁.pair_linear =
      (λ_ N₁.X).hom := by
    have h := congrArg (fun t => (λ_ N₁.X).hom ≫ t) hz₁
    simpa using h
  have hpt₂ : (η[A] ≫ d₂.copair) ▷ N₂.X ≫
      zigContract A d₂.pair d₂.pair_linear =
      (λ_ N₂.X).hom := by
    have h := congrArg (fun t => (λ_ N₂.X).hom ≫ t) hz₂
    simpa using h
  apply modTensor_hom_ext A N₁ N₂
  have hslide : modTensorπ A N₁ N₂ ≫
      (λ_ (modTensor A N₁ N₂)).inv ≫
      ((η[A] ≫ (tensorDatum A d₁ d₂).copair) ▷
        modTensor A N₁ N₂) =
      (λ_ (N₁.X ⊗ N₂.X)).inv ≫
        ((η[A] ≫ (tensorDatum A d₁ d₂).copair) ▷
          (N₁.X ⊗ N₂.X)) ≫
        ((modTensor A (modTensorMod A N₁ N₂)
            (modTensorMod A N₁' N₂')) ◁ modTensorπ A N₁ N₂) := by
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange]
  have hcop : (tensorDatum A d₁ d₂).copair =
      tensorCopair A d₁ d₂ := rfl
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (modTensorπ A N₁ N₂), hslide, hcop, tensorCopair_point,
    Category.assoc, Category.assoc]
  have hμnat : ((η[A] ≫ d₁.copair ⊗ₘ η[A] ≫ d₂.copair) ▷
      (N₁.X ⊗ N₂.X)) ≫
      tensorμ (modTensor A N₁ N₁') (modTensor A N₂ N₂')
        N₁.X N₂.X =
      tensorμ (𝟙_ D) (𝟙_ D) N₁.X N₂.X ≫
        (((η[A] ≫ d₁.copair) ▷ N₁.X) ⊗ₘ
          ((η[A] ≫ d₂.copair) ▷ N₂.X)) := by
    simpa using tensorμ_natural (η[A] ≫ d₁.copair)
      (η[A] ≫ d₂.copair) (𝟙 N₁.X) (𝟙 N₂.X)
  have hcoh : (λ_ (N₁.X ⊗ N₂.X)).inv ≫
      ((λ_ (𝟙_ D)).inv ▷ (N₁.X ⊗ N₂.X)) ≫
      tensorμ (𝟙_ D) (𝟙_ D) N₁.X N₂.X ≫
      ((λ_ N₁.X).hom ⊗ₘ (λ_ N₂.X).hom) = 𝟙 (N₁.X ⊗ N₂.X) := by
    simp only [tensorμ, braiding_tensorUnit_left]
    monoidal
  rw [comp_whiskerRight]
  rw [comp_whiskerRight]
  rw [Category.assoc, Category.assoc]
  rw [← whisker_exchange_assoc
      (interchange A N₁ N₁' N₂ N₂') (modTensorπ A N₁ N₂)]
  rw [interchange_zigContract A d₁ d₂]
  have hfinal : (λ_ (N₁.X ⊗ N₂.X)).inv ≫
      ((λ_ (𝟙_ D)).inv ▷ (N₁.X ⊗ N₂.X)) ≫
      ((η[A] ≫ d₁.copair ⊗ₘ η[A] ≫ d₂.copair) ▷
        (N₁.X ⊗ N₂.X)) ≫
      tensorμ (modTensor A N₁ N₁') (modTensor A N₂ N₂')
        N₁.X N₂.X ≫
      (zigContract A d₁.pair d₁.pair_linear ⊗ₘ
        zigContract A d₂.pair d₂.pair_linear) ≫
      modTensorπ A N₁ N₂ =
      modTensorπ A N₁ N₂ ≫ 𝟙 (modTensor A N₁ N₂) := by
    rw [reassoc_of% hμnat,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      hpt₁, hpt₂, reassoc_of% hcoh, Category.comp_id]
  exact hfinal

/-- **The tensor datum inherits the carrier zag identity.** -/
theorem tensorDatum_carrier_zag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂')
    (hz₁ : (ρ_ N₁'.X).inv ≫ (N₁'.X ◁ (η[A] ≫ d₁.copair)) ≫
      zagContract A d₁.pair d₁.pair_linear = 𝟙 N₁'.X)
    (hz₂ : (ρ_ N₂'.X).inv ≫ (N₂'.X ◁ (η[A] ≫ d₂.copair)) ≫
      zagContract A d₂.pair d₂.pair_linear = 𝟙 N₂'.X) :
    (ρ_ (modTensor A N₁' N₂')).inv ≫
      (modTensor A N₁' N₂' ◁
        (η[A] ≫ (tensorDatum A d₁ d₂).copair)) ≫
      zagContract A (tensorDatum A d₁ d₂).pair
        (tensorDatum A d₁ d₂).pair_linear =
      𝟙 (modTensor A N₁' N₂') := by
  have hpt₁ : N₁'.X ◁ (η[A] ≫ d₁.copair) ≫
      zagContract A d₁.pair d₁.pair_linear =
      (ρ_ N₁'.X).hom := by
    have h := congrArg (fun t => (ρ_ N₁'.X).hom ≫ t) hz₁
    simpa using h
  have hpt₂ : N₂'.X ◁ (η[A] ≫ d₂.copair) ≫
      zagContract A d₂.pair d₂.pair_linear =
      (ρ_ N₂'.X).hom := by
    have h := congrArg (fun t => (ρ_ N₂'.X).hom ≫ t) hz₂
    simpa using h
  apply modTensor_hom_ext A N₁' N₂'
  have hslide : modTensorπ A N₁' N₂' ≫
      (ρ_ (modTensor A N₁' N₂')).inv ≫
      (modTensor A N₁' N₂' ◁
        (η[A] ≫ (tensorDatum A d₁ d₂).copair)) =
      (ρ_ (N₁'.X ⊗ N₂'.X)).inv ≫
        ((N₁'.X ⊗ N₂'.X) ◁
          (η[A] ≫ (tensorDatum A d₁ d₂).copair)) ≫
        (modTensorπ A N₁' N₂' ▷
          (modTensor A (modTensorMod A N₁ N₂)
            (modTensorMod A N₁' N₂'))) := by
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]
  have hcop : (tensorDatum A d₁ d₂).copair =
      tensorCopair A d₁ d₂ := rfl
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (modTensorπ A N₁' N₂'), hslide, hcop, tensorCopair_point,
    Category.assoc, Category.assoc]
  have hμnat : ((N₁'.X ⊗ N₂'.X) ◁
      (η[A] ≫ d₁.copair ⊗ₘ η[A] ≫ d₂.copair)) ≫
      tensorμ N₁'.X N₂'.X (modTensor A N₁ N₁')
        (modTensor A N₂ N₂') =
      tensorμ N₁'.X N₂'.X (𝟙_ D) (𝟙_ D) ≫
        ((N₁'.X ◁ (η[A] ≫ d₁.copair)) ⊗ₘ
          (N₂'.X ◁ (η[A] ≫ d₂.copair))) := by
    simpa using tensorμ_natural (𝟙 N₁'.X) (𝟙 N₂'.X)
      (η[A] ≫ d₁.copair) (η[A] ≫ d₂.copair)
  have hcoh : (ρ_ (N₁'.X ⊗ N₂'.X)).inv ≫
      ((N₁'.X ⊗ N₂'.X) ◁ (λ_ (𝟙_ D)).inv) ≫
      tensorμ N₁'.X N₂'.X (𝟙_ D) (𝟙_ D) ≫
      ((ρ_ N₁'.X).hom ⊗ₘ (ρ_ N₂'.X).hom) =
      𝟙 (N₁'.X ⊗ N₂'.X) := by
    simp only [tensorμ, braiding_tensorUnit_right]
    monoidal
  rw [MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.whiskerLeft_comp]
  rw [Category.assoc, Category.assoc]
  rw [whisker_exchange_assoc
      (modTensorπ A N₁' N₂') (interchange A N₁ N₁' N₂ N₂')]
  rw [interchange_zagContract A d₁ d₂]
  have hfinal : (ρ_ (N₁'.X ⊗ N₂'.X)).inv ≫
      ((N₁'.X ⊗ N₂'.X) ◁ (λ_ (𝟙_ D)).inv) ≫
      ((N₁'.X ⊗ N₂'.X) ◁
        (η[A] ≫ d₁.copair ⊗ₘ η[A] ≫ d₂.copair)) ≫
      tensorμ N₁'.X N₂'.X (modTensor A N₁ N₁')
        (modTensor A N₂ N₂') ≫
      (zagContract A d₁.pair d₁.pair_linear ⊗ₘ
        zagContract A d₂.pair d₂.pair_linear) ≫
      modTensorπ A N₁' N₂' =
      modTensorπ A N₁' N₂' ≫ 𝟙 (modTensor A N₁' N₂') := by
    rw [reassoc_of% hμnat,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      hpt₁, hpt₂, reassoc_of% hcoh, Category.comp_id]
  exact hfinal

/-- **The tensor of zigzag data is a zigzag datum** (Deligne
1.15, tensor part, in triangle form). -/
theorem tensorDatum_zigzag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {N₁ : Mod D A} {N₂ : Mod D A}
    {N₁' : Mod D A} {N₂' : Mod D A}
    (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂')
    (hz₁ : ModZigzagDatum A d₁) (hz₂ : ModZigzagDatum A d₂) :
    ModZigzagDatum A (tensorDatum A d₁ d₂) :=
  modZigzagDatum_of_carrier A
    (tensorDatum_carrier_zig A d₁ d₂
      (zigzag_carrier_zig A hz₁) (zigzag_carrier_zig A hz₂))
    (tensorDatum_carrier_zag A d₁ d₂
      (zigzag_carrier_zag A hz₁) (zigzag_carrier_zag A hz₂))

end RS
