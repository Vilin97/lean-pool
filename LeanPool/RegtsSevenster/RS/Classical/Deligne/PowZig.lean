/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowTriangle

/-!
# The carrier calculus of the power chain

The scalar-based copairing powers of a duality datum, and the two
carrier-level operations the chain is built from: contraction
against a pairing (`RS.carrierContract`) and insertion of a
copairing (`RS.zigCarrier`), with their naturality in the module
and their evaluation on scalars.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The scalar-based copairing power**: the base acts on the
chain unit. -/
noncomputable def powCopairA
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) : A ⟶ powStage A M M' n :=
  (ρ_ A).inv ≫ (A ◁ powUnitStage A M M' d n) ≫
    modTensorAct A (modPowMod A M.X n) (modPowMod A M'.X n)

/-- The bottom copairing power is the copairing, through the
singleton stages. -/
theorem powCopairA_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    powCopairA A M M' d 0 =
      d.copair ≫ modTensorMap A (toModPowModZero A M)
        (toModPowModZero A M') := by
  rw [powCopairA]
  change (ρ_ A).inv ≫ (A ◁ (copairUnit A M M' d ≫
      modTensorMap A (toModPowModZero A M)
        (toModPowModZero A M'))) ≫
    modTensorAct A (modPowMod A M.X 0) (modPowMod A M'.X 0) = _
  rw [copairUnit, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]
  rw [show (A ◁ modTensorMap A (toModPowModZero A M)
        (toModPowModZero A M')) ≫
      modTensorAct A (modPowMod A M.X 0) (modPowMod A M'.X 0) =
    modTensorAct A M M' ≫ modTensorMap A (toModPowModZero A M)
        (toModPowModZero A M') from
    (modTensorAct_map A (toModPowModZero A M)
      (toModPowModZero A M')).symm]
  have hlin' : μ[A] ≫ d.copair =
      (A ◁ d.copair) ≫ modTensorAct A M M' := d.copair_linear
  rw [← reassoc_of% hlin']
  rw [← Category.assoc, ← Category.assoc]
  rw [show ((ρ_ A).inv ≫ (A ◁ η[A])) ≫ μ[A] = 𝟙 A from by
    rw [Category.assoc, MonObj.mul_one, Iso.inv_hom_id]]
  rw [Category.id_comp]

section CarrierZig

/-- The carrier contraction: the module crosses the relative
tensor, pairs against it, and the scalar acts. -/
noncomputable def carrierContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A) :
    M.X ⊗ modTensor A M' M ⟶ M.X :=
  modTensorWhiskerDesc A M' M M.X
    ((β_ M.X (M'.X ⊗ M.X)).hom ≫
      ((modTensorπ A M' M ≫ p) ▷ M.X) ≫ actLeft A M.X)
    (by
      have hw : ∀ (w : (M'.X ⊗ A) ⊗ M.X ⟶ M'.X ⊗ M.X),
          (M.X ◁ w) ≫ (β_ M.X (M'.X ⊗ M.X)).hom ≫
            ((modTensorπ A M' M ≫ p) ▷ M.X) ≫
            actLeft A M.X =
          (β_ M.X ((M'.X ⊗ A) ⊗ M.X)).hom ≫
            ((w ≫ modTensorπ A M' M ≫ p) ▷ M.X) ≫
            actLeft A M.X := by
        intro w
        rw [BraidedCategory.braiding_naturality_right_assoc,
          ← comp_whiskerRight_assoc]
      rw [hw, hw]
      have hcond : modTensorLegM A M' M ≫
          modTensorπ A M' M ≫ p =
        modTensorLegN A M' M ≫ modTensorπ A M' M ≫ p := by
        rw [← Category.assoc, modTensor_condition,
          Category.assoc]
      exact congrArg (fun t =>
        (β_ M.X ((M'.X ⊗ A) ⊗ M.X)).hom ≫ (t ▷ M.X) ≫
        actLeft A M.X) hcond)

/-- Defining equation of the carrier contraction. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_π_carrierContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A) :
    (M.X ◁ modTensorπ A M' M) ≫ carrierContract A p =
      (β_ M.X (M'.X ⊗ M.X)).hom ≫
        ((modTensorπ A M' M ≫ p) ▷ M.X) ≫ actLeft A M.X :=
  whiskerLeft_modTensorπ_whiskerDesc A M' M M.X _ _

/-- **The carrier zigzag** of a copairing and a pairing: insert
the copairing, cross, contract. -/
noncomputable def zigCarrier
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M' M)
    (p : modTensor A M' M ⟶ A) : M.X ⟶ M.X :=
  (λ_ M.X).inv ≫ ((η[A] ≫ c) ▷ M.X) ≫
    (β_ (modTensor A M' M) M.X).hom ≫ carrierContract A p

/-- The singleton stage maps back onto the module. -/
noncomputable def fromModPowModZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (M : Mod D A) :
    modPowMod A M.X 0 ⟶ M :=
  Mod.Hom.mk' ((modPowOne A M.X).hom)
    (modPowAct_modPowOne A M.X)

/-- The carrier contraction transports along module maps of the
dual pair. -/
theorem carrierContract_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    {N N' : Mod D A}
    (e : M ⟶ N) (f : N ⟶ M) (f' : N' ⟶ M')
    (hfe : f ≫ e = 𝟙 N)
    (p : modTensor A M' M ⟶ A) (p' : modTensor A N' N ⟶ A)
    (hp' : modTensorMap A f' f ≫ p = p') :
    carrierContract A p' =
      (f.hom ▷ modTensor A N' N) ≫
      (M.X ◁ modTensorMap A f' f) ≫
      carrierContract A p ≫ e.hom := by
  apply modTensor_whisker_hom_ext A N' N N.X
  rw [whiskerLeft_π_carrierContract]
  have hpush : (N.X ◁ modTensorπ A N' N) ≫
      (f.hom ▷ modTensor A N' N) =
    (f.hom ▷ (N'.X ⊗ N.X)) ≫ (M.X ◁ modTensorπ A N' N) :=
    whisker_exchange _ _
  rw [reassoc_of% hpush]
  have hmerge : (M.X ◁ modTensorπ A N' N) ≫
      (M.X ◁ modTensorMap A f' f) =
    M.X ◁ ((f'.hom ⊗ₘ f.hom) ≫ modTensorπ A M' M) := by
    rw [← MonoidalCategory.whiskerLeft_comp, modTensorπ_map]
  rw [reassoc_of% hmerge, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, whiskerLeft_π_carrierContract_assoc]
  have hs1 : (M.X ◁ (f'.hom ⊗ₘ f.hom)) ≫
      (β_ M.X (M'.X ⊗ M.X)).hom =
    (β_ M.X (N'.X ⊗ N.X)).hom ≫
      ((f'.hom ⊗ₘ f.hom) ▷ M.X) := by
    rw [BraidedCategory.braiding_naturality_right]
  rw [reassoc_of% hs1]
  have hs2 : (f.hom ▷ (N'.X ⊗ N.X)) ≫
      (β_ M.X (N'.X ⊗ N.X)).hom =
    (β_ N.X (N'.X ⊗ N.X)).hom ≫
      ((N'.X ⊗ N.X) ◁ f.hom) := by
    rw [BraidedCategory.braiding_naturality_left]
  rw [reassoc_of% hs2]
  refine congrArg (CategoryStruct.comp _) ?_
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  have := f.isModHom
  rw [show (A ◁ f.hom) ≫ actLeft A M.X ≫ e.hom =
      actLeft A N.X ≫ f.hom ≫ e.hom from by
    rw [← actLeft_natural_assoc]]
  rw [show f.hom ≫ e.hom = 𝟙 N.X from by
    have h := congrArg Mod.Hom.hom hfe
    exact h]
  rw [Category.comp_id]
  have hfinal : ((f'.hom ⊗ₘ f.hom) ▷ N.X) ≫
      ((modTensorπ A M' M ≫ p) ▷ N.X) =
    ((modTensorπ A N' N ≫ p') ▷ N.X) := by
    rw [← comp_whiskerRight]
    congr 1
    rw [← Category.assoc, ← modTensorπ_map, Category.assoc,
      hp']
  rw [reassoc_of% hfinal]

/-- The carrier zigzag transports along module isomorphisms of
the dual pair. -/
theorem zigCarrier_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    {N N' : Mod D A}
    (e : M ⟶ N) (f : N ⟶ M) (e' : M' ⟶ N') (f' : N' ⟶ M')
    (hfe : f ≫ e = 𝟙 N) (hef : e ≫ f = 𝟙 M)
    (he'f' : e' ≫ f' = 𝟙 M')
    (c : A ⟶ modTensor A M' M) (p : modTensor A M' M ⟶ A)
    (c' : A ⟶ modTensor A N' N) (p' : modTensor A N' N ⟶ A)
    (hc' : c' = c ≫ modTensorMap A e' e)
    (hp' : modTensorMap A f' f ≫ p = p') :
    zigCarrier A c' p' =
      f.hom ≫ zigCarrier A c p ≫ e.hom := by
  rw [zigCarrier, zigCarrier,
    carrierContract_map A e f f' hfe p p' hp', hc']
  rw [Category.assoc, comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc]
  have hs2 : (modTensorMap A e' e ▷ N.X) ≫
      (β_ (modTensor A N' N) N.X).hom =
    (β_ (modTensor A M' M) N.X).hom ≫
      (N.X ◁ modTensorMap A e' e) := by
    rw [BraidedCategory.braiding_naturality_left]
  rw [reassoc_of% hs2]
  have hs3 : (N.X ◁ modTensorMap A e' e) ≫
      (f.hom ▷ modTensor A N' N) =
    (f.hom ▷ modTensor A M' M) ≫
      (M.X ◁ modTensorMap A e' e) :=
    whisker_exchange _ _
  rw [reassoc_of% hs3]
  have hs4 : (M.X ◁ modTensorMap A e' e) ≫
      (M.X ◁ modTensorMap A f' f) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← modTensorMap_comp, he'f', hef, modTensorMap_id,
      MonoidalCategory.whiskerLeft_id]
  rw [reassoc_of% hs4]
  have hs5 : (β_ (modTensor A M' M) N.X).hom ≫
      (f.hom ▷ modTensor A M' M) =
    (modTensor A M' M ◁ f.hom) ≫
      (β_ (modTensor A M' M) M.X).hom := by
    rw [BraidedCategory.braiding_naturality_right]
  rw [reassoc_of% hs5]
  have hs6a : (c ▷ N.X) ≫ (modTensor A M' M ◁ f.hom) =
      (A ◁ f.hom) ≫ (c ▷ M.X) :=
    (whisker_exchange _ _).symm
  rw [reassoc_of% hs6a]
  have hs6b : (η[A] ▷ N.X) ≫ (A ◁ f.hom) =
      (𝟙_ D ◁ f.hom) ≫ (η[A] ▷ M.X) :=
    (whisker_exchange _ _).symm
  rw [reassoc_of% hs6b]
  have hlam : (λ_ N.X).inv ≫ (𝟙_ D ◁ f.hom) =
      f.hom ≫ (λ_ M.X).inv := by
    rw [leftUnitor_inv_naturality]
  rw [reassoc_of% hlam]
  conv_rhs => rw [comp_whiskerRight]
  simp only [Category.assoc]

/-- The carrier contraction is the crossing, the pairing, and the
action, already at the quotient. -/
theorem carrierContract_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (p : modTensor A M' M ⟶ A) :
    carrierContract A p =
      (β_ M.X (modTensor A M' M)).hom ≫ (p ▷ M.X) ≫
        actLeft A M.X := by
  apply modTensor_whisker_hom_ext A M' M M.X
  rw [whiskerLeft_π_carrierContract]
  have hβ : (M.X ◁ modTensorπ A M' M) ≫
      (β_ M.X (modTensor A M' M)).hom =
    (β_ M.X (M'.X ⊗ M.X)).hom ≫
      (modTensorπ A M' M ▷ M.X) := by
    rw [BraidedCategory.braiding_naturality_right]
  rw [reassoc_of% hβ, ← comp_whiskerRight_assoc]

/-- **The scalar form of the carrier zigzag**: the zigzag is the
action of the paired copairing scalar. -/
theorem zigCarrier_scalar
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (c : A ⟶ modTensor A M' M)
    (p : modTensor A M' M ⟶ A) :
    zigCarrier A c p =
      (λ_ M.X).inv ≫ ((η[A] ≫ c ≫ p) ▷ M.X) ≫
        actLeft A M.X := by
  rw [zigCarrier, carrierContract_eq]
  have hββ : (β_ (modTensor A M' M) M.X).hom ≫
      (β_ M.X (modTensor A M' M)).hom = 𝟙 _ :=
    SymmetricCategory.symmetry _ _
  rw [reassoc_of% hββ, ← comp_whiskerRight_assoc]
  exact congrArg (fun t =>
    (λ_ M.X).inv ≫ (t ▷ M.X) ≫ actLeft A M.X)
    (Category.assoc _ _ _)

end CarrierZig

end RS
