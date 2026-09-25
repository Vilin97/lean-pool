/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.InterchangeAct
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBGr

/-!
# The seed entries of the splitting data

The three entry maps of the splitting algebra: the base algebra,
the module, and the dual module enter the two-index chain stages
through the seed element.  These are the stage-level precursors
of the `ofBase`, `ins` and `ins'` fields of the splitting data of
the Key Lemma.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The base entry**: the base algebra acts on the seed element
in the bottom stage. -/
noncomputable def chainBaseStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    A ⟶ chainStage2 A M M' 0 0 :=
  (ρ_ A).inv ≫
    MonoidalCategory.whiskerLeft A
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
    modTensorAct A (symPowMod A M'.X 0) (symPowMod A M.X 0)

/-- **The module entry**: the module joins the seed element in
the second slot, one degree up. -/
noncomputable def chainSeedQ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    M.X ⟶ chainStage2 A M M' 0 1 :=
  (ρ_ M.X).inv ≫
    MonoidalCategory.whiskerLeft M.X
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
    chainInsQ A M M' 0 0

/-- **The dual entry**: the dual module joins the seed element in
the first slot, one degree down. -/
noncomputable def chainSeedP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    M'.X ⟶ chainStage2 A M M' 1 0 :=
  (ρ_ M'.X).inv ≫
    MonoidalCategory.whiskerLeft M'.X
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
    chainInsP A M M' 0 0

/-- The unit of the base enters as the seed element. -/
theorem unit_chainBaseStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    η[A] ≫ chainBaseStage A M M' d = chainSeed A M M' d := by
  have h1 : η[A] ≫ (ρ_ A).inv =
      (ρ_ (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerRight η[A] (𝟙_ D) :=
    rightUnitor_inv_naturality _
  have h2 : MonoidalCategory.whiskerRight η[A] (𝟙_ D) ≫
      MonoidalCategory.whiskerLeft A
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) =
    MonoidalCategory.whiskerLeft (𝟙_ D)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      MonoidalCategory.whiskerRight η[A]
        (chainStage2 A M M' 0 0) :=
    (whisker_exchange _ _).symm
  have h3 : MonoidalCategory.whiskerRight η[A]
      (chainStage2 A M M' 0 0) ≫
      modTensorAct A (symPowMod A M'.X 0) (symPowMod A M.X 0) =
    (λ_ (chainStage2 A M M' 0 0)).hom := modTensorAct_one A _ _
  have h4 : MonoidalCategory.whiskerLeft (𝟙_ D)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (λ_ (chainStage2 A M M' 0 0)).hom =
    (λ_ (𝟙_ D)).hom ≫ chainSeed A M M' d :=
    leftUnitor_naturality _
  erw [chainBaseStage, reassoc_of% h1, reassoc_of% h2]
  exact (congrArg (fun t => (ρ_ (𝟙_ D)).inv ≫
      MonoidalCategory.whiskerLeft (𝟙_ D)
        (Y₂ := chainStage2 A M M' 0 0)
        (chainSeed A M M' d) ≫ t) h3).trans
    ((congrArg (fun t => (ρ_ (𝟙_ D)).inv ≫ t) h4).trans
      (by rw [unitors_equal]; exact Iso.inv_hom_id_assoc _ _))

/-! ## The entries against the base action -/

/-- The base action commutes with the stage transports. -/
theorem chainStage2Cast_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {p q p' q' : ℕ} (hp : p = p') (hq : q = q') :
    (A ◁ chainStage2Cast A M M' hp hq) ≫
        modTensorAct A (symPowMod A M'.X p') (symPowMod A M.X q') =
      modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X q) ≫
        chainStage2Cast A M M' hp hq := by
  subst hp hq
  erw [chainStage2Cast_rfl, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id]

/-- **The two-index transition is linear over the base**: acting
on a stage and raising is raising and acting. -/
theorem chainDelta2_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (p q : ℕ) :
    (A ◁ chainDelta2 A M M' d p q) ≫
        modTensorAct A (symPowMod A M'.X (p + 1)) (symPowMod A M.X (q + 1)) =
      modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X q) ≫
        chainDelta2 A M M' d p q := by
  have ha : (A ◁ chainMul2 A M M' p q 0 0) ≫
      modTensorAct A (symPowMod A M'.X (p + 1))
        (symPowMod A M.X (q + 1)) =
      (α_ A (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        (modTensorAct A (symPowMod A M'.X p)
            (symPowMod A M.X q) ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p q 0 0 := by
    have h := chainMul2_actLeft A M M' p q 0 0
    have h' := congrArg (fun t => (α_ A
        (modTensor A (symPowMod A M'.X p) (symPowMod A M.X q))
        (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 0))).inv ≫ t) h
    exact (h'.trans (Iso.inv_hom_id_assoc _ _)).symm
  have hc : (A ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (α_ A (chainStage2 A M M' p q)
        (chainStage2 A M M' 0 0)).inv =
      (α_ A (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerLeft
          (A ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) :=
    associator_inv_naturality_right _ _ _
  have hd : MonoidalCategory.whiskerLeft
        (A ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (modTensorAct A (symPowMod A M'.X p)
          (symPowMod A M.X q) ▷ chainStage2 A M M' 0 0) =
      (modTensorAct A (symPowMod A M'.X p)
          (symPowMod A M.X q) ▷ 𝟙_ D) ≫
        MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) :=
    whisker_exchange _ _
  have he : (A ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ A (chainStage2 A M M' p q) (𝟙_ D)).inv =
      (ρ_ (A ⊗ chainStage2 A M M' p q)).inv := by
    monoidal
  have hf : (ρ_ (A ⊗ chainStage2 A M M' p q)).inv ≫
      (modTensorAct A (symPowMod A M'.X p)
          (symPowMod A M.X q) ▷ 𝟙_ D) =
      modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X q) ≫
        (ρ_ (chainStage2 A M M' p q)).inv :=
    (rightUnitor_inv_naturality _).symm
  have hsplit : A ◁ chainDelta2 A M M' d p q =
      (A ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (A ◁ MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        (A ◁ chainMul2 A M M' p q 0 0) := by
    rw [chainDelta2, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp]
  refine Eq.trans (eq_whisker hsplit
    (modTensorAct A (symPowMod A M'.X (p + 1))
      (symPowMod A M.X (q + 1)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ ha)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hc _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (eq_whisker hd _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker he _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hf _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (by rw [chainDelta2]; rfl)

/-- **Multiplication by the base entry on the left** is the stage
action followed by the transition, up to the index transport. -/
theorem chainBaseStage_mul2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (p q : ℕ) :
    (chainBaseStage A M M' d ▷ chainStage2 A M M' p q) ≫
        chainMul2 A M M' 0 0 p q =
      modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X q) ≫
        chainDelta2 A M M' d p q ≫
        chainStage2Cast A M M' (by omega : p + 1 = 0 + 1 + p)
          (by omega : q + 1 = 0 + 1 + q) := by
  have hsplit : chainBaseStage A M M' d ▷
        chainStage2 A M M' p q =
      ((ρ_ A).inv ▷ chainStage2 A M M' p q) ≫
        (MonoidalCategory.whiskerLeft A
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ▷
          chainStage2 A M M' p q) ≫
        (modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 0) ▷ chainStage2 A M M' p q) := by
    erw [chainBaseStage, MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.comp_whiskerRight]
    rfl
  have hb : (modTensorAct A (symPowMod A M'.X 0)
        (symPowMod A M.X 0) ▷ chainStage2 A M M' p q) ≫
      chainMul2 A M M' 0 0 p q =
      (α_ A (chainStage2 A M M' 0 0)
          (chainStage2 A M M' p q)).hom ≫
        (A ◁ chainMul2 A M M' 0 0 p q) ≫
        modTensorAct A (symPowMod A M'.X (0 + 1 + p))
          (symPowMod A M.X (0 + 1 + q)) :=
    chainMul2_actLeft A M M' 0 0 p q
  have hm : (MonoidalCategory.whiskerLeft A
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ▷
        chainStage2 A M M' p q) ≫
      (α_ A (chainStage2 A M M' 0 0)
        (chainStage2 A M M' p q)).hom =
      (α_ A (𝟙_ D) (chainStage2 A M M' p q)).hom ≫
        (A ◁ (chainSeed A M M' d ▷ chainStage2 A M M' p q)) :=
    associator_naturality_middle _ _ _
  have hwm : (A ◁ (chainSeed A M M' d ▷
        chainStage2 A M M' p q)) ≫
      (A ◁ chainMul2 A M M' 0 0 p q) =
      A ◁ ((chainSeed A M M' d ▷ chainStage2 A M M' p q) ≫
        chainMul2 A M M' 0 0 p q) :=
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm
  have hA : A ◁ ((chainSeed A M M' d ▷
        chainStage2 A M M' p q) ≫ chainMul2 A M M' 0 0 p q) =
      A ◁ ((λ_ (chainStage2 A M M' p q)).hom ≫
        chainDelta2 A M M' d p q ≫
        chainStage2Cast A M M' (by omega : p + 1 = 0 + 1 + p)
          (by omega : q + 1 = 0 + 1 + q)) :=
    congrArg (fun t : 𝟙_ D ⊗ chainStage2 A M M' p q ⟶
        chainStage2 A M M' (0 + 1 + p) (0 + 1 + q) => A ◁ t)
      (chainSeed_mul2_left A M M' d p q)
  have hr : ((ρ_ A).inv ▷ chainStage2 A M M' p q) ≫
      (α_ A (𝟙_ D) (chainStage2 A M M' p q)).hom =
      A ◁ (λ_ (chainStage2 A M M' p q)).inv := by
    monoidal
  have hmerge : (A ◁ (λ_ (chainStage2 A M M' p q)).inv) ≫
      (A ◁ ((λ_ (chainStage2 A M M' p q)).hom ≫
        chainDelta2 A M M' d p q ≫
        chainStage2Cast A M M' (by omega : p + 1 = 0 + 1 + p)
          (by omega : q + 1 = 0 + 1 + q))) =
      A ◁ (chainDelta2 A M M' d p q ≫
        chainStage2Cast A M M' (by omega : p + 1 = 0 + 1 + p)
          (by omega : q + 1 = 0 + 1 + q)) :=
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
      (congrArg (fun t : chainStage2 A M M' p q ⟶
          chainStage2 A M M' (0 + 1 + p) (0 + 1 + q) => A ◁ t)
        (Iso.inv_hom_id_assoc _ _))
  have hcast : (A ◁ chainStage2Cast A M M'
        (by omega : p + 1 = 0 + 1 + p)
        (by omega : q + 1 = 0 + 1 + q)) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + p))
        (symPowMod A M.X (0 + 1 + q)) =
      modTensorAct A (symPowMod A M'.X (p + 1))
        (symPowMod A M.X (q + 1)) ≫
        chainStage2Cast A M M'
          (by omega : p + 1 = 0 + 1 + p)
          (by omega : q + 1 = 0 + 1 + q) :=
    chainStage2Cast_actLeft A M M' _ _
  refine Eq.trans (eq_whisker hsplit
    (chainMul2 A M M' 0 0 p q)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hb)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hm _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (eq_whisker hwm _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (eq_whisker hA _))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hr _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hmerge _) ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hcast) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (chainDelta2_actLeft A M M' d p q) _) ?_
  exact Category.assoc _ _ _

/-! ## The letter action against the insertions -/

section LetterAct

/-- **The insertion is compatible with the action on the inserted
letter**: acting on the letter and inserting is inserting and
acting on the enlarged power. -/
theorem symInsL_actLetter
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X] (n : ℕ) :
    (actLeft A X ▷ symPow A X (n + 1)) ≫ symInsL A X n =
      (α_ A X (symPow A X (n + 1))).hom ≫
        (A ◁ symInsL A X n) ≫ symPowAct A X (n + 1) := by
  have h1 : actLeft A X ≫ (symPowOne A X).inv =
      (A ◁ (symPowOne A X).inv) ≫ symPowAct A X 0 :=
    actLeft_symPowOne_inv A X
  have h2 : (symPowAct A X 0 ▷ symPow A X (n + 1)) ≫
      symMul A X 1 (n + 1) =
      (α_ A (symPow A X 1) (symPow A X (n + 1))).hom ≫
        (A ◁ symMul A X 1 (n + 1)) ≫
        symPowAct A X (1 + n) := by
    have h := symMul_actLeft A X 0 n
    have h' := congrArg (fun t =>
      (α_ A (symPow A X (0 + 1))
        (symPow A X (n + 1))).hom ≫ t) h
    exact (Iso.hom_inv_id_assoc _ _).symm.trans h'
  have h3 : symPowAct A X (1 + n) ≫
      symPowCast A X (by omega : 1 + (n + 1) = n + 2) =
      (A ◁ symPowCast A X
        (by omega : 1 + (n + 1) = n + 2)) ≫
        symPowAct A X (n + 1) :=
    symPowAct_symPowCast A X (by omega)
  have h4 : ((A ◁ (symPowOne A X).inv) ▷ symPow A X (n + 1)) ≫
      (α_ A (symPow A X 1) (symPow A X (n + 1))).hom =
      (α_ A X (symPow A X (n + 1))).hom ≫
        (A ◁ ((symPowOne A X).inv ▷ symPow A X (n + 1))) :=
    associator_naturality_middle _ _ _
  rw [symInsL, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.comp_whiskerRight_assoc, h1,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% h2, h3, reassoc_of% h4]

end LetterAct

/-- **The first-slot insertion is linear over the base in the
letter**: acting on the inserted dual module and inserting is
inserting and acting on the raised stage. -/
theorem chainInsP_actLetter
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) (p q : ℕ) :
    (actLeft A M'.X ▷ chainStage2 A M M' p q) ≫
        chainInsP A M M' p q =
      (α_ A M'.X (chainStage2 A M M' p q)).hom ≫
        (A ◁ chainInsP A M M' p q) ≫
        modTensorAct A (symPowMod A M'.X (p + 1)) (symPowMod A M.X q) := by
  have l1 : ((A ⊗ M'.X) ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q)) ≫
        (actLeft A M'.X ▷ chainStage2 A M M' p q) =
      (actLeft A M'.X ▷
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))) ≫
        (M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) :=
    whisker_exchange _ _
  have l3 : (actLeft A M'.X ▷
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))) ≫
        (α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv =
      (α_ (A ⊗ M'.X) (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((actLeft A M'.X ▷ symPow A M'.X (p + 1)) ▷
          symPow A M.X (q + 1)) :=
    associator_inv_naturality_left _ _ _
  have r1 : ((A ⊗ M'.X) ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q)) ≫
        (α_ A M'.X (chainStage2 A M M' p q)).hom =
      (α_ A M'.X
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))).hom ≫
        (A ◁ (M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q))) :=
    associator_naturality_right _ _ _
  have r4 : (A ◁ modTensorπ A (symPowMod A M'.X (p + 1))
        (symPowMod A M.X q)) ≫
        modTensorAct A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q) =
      ((α_ A (symPow A M'.X (p + 2))
          (symPow A M.X (q + 1))).inv ≫
        (symPowAct A M'.X (p + 1) ▷ symPow A M.X (q + 1))) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q) :=
    whiskerLeft_modTensorπ_act A _ _
  have hmid : (A ◁ (symInsL A M'.X p ▷
        symPow A M.X (q + 1))) ≫
        (α_ A (symPow A M'.X (p + 2))
          (symPow A M.X (q + 1))).inv =
      (α_ A (M'.X ⊗ symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((A ◁ symInsL A M'.X p) ▷ symPow A M.X (q + 1)) :=
    associator_inv_naturality_middle _ _ _
  have hcoh : (α_ (A ⊗ M'.X) (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1))).inv ≫
        ((α_ A M'.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) =
      (α_ A M'.X
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))).hom ≫
        (A ◁ (α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv) ≫
        (α_ A (M'.X ⊗ symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv := by
    monoidal
  refine (cancel_epi ((A ⊗ M'.X) ◁
    modTensorπ A (symPowMod A M'.X p)
      (symPowMod A M.X q))).mp ?_
  -- The action side reduces to the symmetric-power level.
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker l1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (whiskerLeft_π_chainInsP A M M' p q)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker l3 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    ((Category.assoc _ _ _).symm.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _).symm _))) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (congrArg (fun t : (A ⊗ M'.X) ⊗ symPow A M'.X (p + 1) ⟶
        symPow A M'.X (p + 2) => t ▷ symPow A M.X (q + 1))
      (symInsL_actLetter A M'.X p)) _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    ((MonoidalCategory.comp_whiskerRight _ _ _).trans
      (whisker_eq _
        (MonoidalCategory.comp_whiskerRight _ _ _))) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hcoh _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  -- The insertion side reduces to the same normal form.
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker r1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (congrArg (fun t : M'.X ⊗
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1)) ⟶
        chainStage2 A M M' (p + 1) q => A ◁ t)
      (whiskerLeft_π_chainInsP A M M' p q)) _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    ((MonoidalCategory.whiskerLeft_comp _ _ _).trans
      (whisker_eq _
        (MonoidalCategory.whiskerLeft_comp _ _ _))) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whisker_eq _ r4))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (whisker_eq _ (Category.assoc _ _ _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (eq_whisker hmid _))) ?_
  exact whisker_eq _ (whisker_eq _ (Category.assoc _ _ _))

/-- **The dual entry is linear over the base**: the action on the
dual module followed by the entry is the entry followed by the
stage action. -/
theorem chainSeedP_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    actLeft A M'.X ≫ chainSeedP A M M' d =
      (A ◁ chainSeedP A M M' d) ≫
        modTensorAct A (symPowMod A M'.X 1) (symPowMod A M.X 0) := by
  have hsplit : chainSeedP A M M' d =
      (ρ_ M'.X).inv ≫
        MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainInsP A M M' 0 0 := rfl
  have h1 : actLeft A M'.X ≫ (ρ_ M'.X).inv =
      (ρ_ (A ⊗ M'.X)).inv ≫ (actLeft A M'.X ▷ 𝟙_ D) :=
    rightUnitor_inv_naturality _
  have h2 : (actLeft A M'.X ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) =
      MonoidalCategory.whiskerLeft (A ⊗ M'.X)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        (actLeft A M'.X ▷ chainStage2 A M M' 0 0) :=
    (whisker_exchange _ _).symm
  have h3 : (actLeft A M'.X ▷ chainStage2 A M M' 0 0) ≫
      chainInsP A M M' 0 0 =
      (α_ A M'.X (chainStage2 A M M' 0 0)).hom ≫
        (A ◁ chainInsP A M M' 0 0) ≫
        modTensorAct A (symPowMod A M'.X 1)
          (symPowMod A M.X 0) :=
    chainInsP_actLetter A M M' 0 0
  have h4 : MonoidalCategory.whiskerLeft (A ⊗ M'.X)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (α_ A M'.X (chainStage2 A M M' 0 0)).hom =
      (α_ A M'.X (𝟙_ D)).hom ≫
        (A ◁ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) :=
    associator_naturality_right _ _ _
  have h5 : (ρ_ (A ⊗ M'.X)).inv ≫ (α_ A M'.X (𝟙_ D)).hom =
      A ◁ (ρ_ M'.X).inv := by
    monoidal
  refine Eq.trans (whisker_eq _ hsplit) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker h1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker h2 _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ h3)) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker h4 _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker h5 _) ?_
  refine Eq.symm ?_
  refine Eq.trans (eq_whisker
    (congrArg (fun t : M'.X ⟶ chainStage2 A M M' 1 0 =>
      A ◁ t) hsplit) _) ?_
  refine Eq.trans (eq_whisker
    ((MonoidalCategory.whiskerLeft_comp _ _ _).trans
      (whisker_eq _
        (MonoidalCategory.whiskerLeft_comp _ _ _))) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (Category.assoc _ _ _)

/-- The braided crossing of a tensor pair past a factor splits
into the crossings of its parts, one on either side of the
carried slot. -/
private theorem letter_cross_struct_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (P Q V T : D) :
    (α_ (P ⊗ Q) V T).inv ≫ ((β_ (P ⊗ Q) V).hom ▷ T) ≫
        (α_ V (P ⊗ Q) T).hom =
      (α_ P Q (V ⊗ T)).hom ≫ (P ◁ (α_ Q V T).inv) ≫
        (P ◁ ((β_ Q V).hom ▷ T)) ≫ (P ◁ (α_ V Q T).hom) ≫
        (α_ P V (Q ⊗ T)).inv ≫ ((β_ P V).hom ▷ (Q ⊗ T)) ≫
        (α_ V P (Q ⊗ T)).hom ≫ (V ◁ (α_ P Q T).inv) := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc]
  monoidal

/-- Acting on a letter destined for the second slot commutes with
the braided crossing: the acting object crosses the first factor
alongside the letter and acts once the letter has entered. -/
private theorem letter_cross_snd_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {P Q V T T' W : D} (u : P ⊗ Q ⟶ Q) (f : Q ⊗ T ⟶ T') (a' : P ⊗ T' ⟶ T')
    (w : V ⊗ T' ⟶ W) (hf : (P ◁ f) ≫ a' =
      (α_ P Q T).inv ≫ (u ▷ T) ≫ f) :
    (u ▷ (V ⊗ T)) ≫ ((α_ Q V T).inv ≫
        ((β_ Q V).hom ▷ T) ≫ (α_ V Q T).hom ≫
        (V ◁ f) ≫ w) =
      (α_ P Q (V ⊗ T)).hom ≫ ((P ◁ (α_ Q V T).inv) ≫
        (P ◁ ((β_ Q V).hom ▷ T)) ≫ (P ◁ (α_ V Q T).hom) ≫
        (P ◁ (V ◁ f)) ≫ ((α_ P V T').inv ≫
          ((β_ P V).hom ▷ T') ≫ (α_ V P T').hom ≫
          (V ◁ a') ≫ w)) := by
  have hfV : (V ◁ (P ◁ f)) ≫ (V ◁ a') =
      (V ◁ (α_ P Q T).inv) ≫ (V ◁ (u ▷ T)) ≫ (V ◁ f) := by
    rw [← MonoidalCategory.whiskerLeft_comp, hf]
    simp only [MonoidalCategory.whiskerLeft_comp]
  rw [associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left,
    MonoidalCategory.comp_whiskerRight_assoc,
    associator_naturality_middle_assoc,
    associator_inv_naturality_right_assoc,
    whisker_exchange_assoc,
    associator_naturality_right_assoc,
    reassoc_of% hfV,
    reassoc_of% (letter_cross_struct_aux P Q V T)]

/-- **The second-slot insertion is linear over the base in the
letter**: acting on the inserted module and inserting is
inserting and acting on the raised stage.  The letter enters the
second slot through the braided crossing, while the descended
action passes through the first factor; over a symmetric base the
two meet in the second slot. -/
theorem chainInsQ_actLetter
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) (p q : ℕ) :
    (actLeft A M.X ▷ chainStage2 A M M' p q) ≫
        chainInsQ A M M' p q =
      (α_ A M.X (chainStage2 A M M' p q)).hom ≫
        (A ◁ chainInsQ A M M' p q) ≫
        modTensorAct A (symPowMod A M'.X p) (symPowMod A M.X (q + 1)) := by
  have hf : (A ◁ symInsL A M.X q) ≫ symPowAct A M.X (q + 1) =
      (α_ A M.X (symPow A M.X (q + 1))).inv ≫
        (actLeft A M.X ▷ symPow A M.X (q + 1)) ≫
        symInsL A M.X q := by
    rw [symInsL_actLetter A M.X q, Iso.inv_hom_id_assoc]
  have l1 : ((A ⊗ M.X) ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q)) ≫
        (actLeft A M.X ▷ chainStage2 A M M' p q) =
      (actLeft A M.X ▷
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))) ≫
        (M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) :=
    whisker_exchange _ _
  have r1 : ((A ⊗ M.X) ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q)) ≫
        (α_ A M.X (chainStage2 A M M' p q)).hom =
      (α_ A M.X
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))).hom ≫
        (A ◁ (M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q))) :=
    associator_naturality_right _ _ _
  have r4 : (A ◁ modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X (q + 1))) ≫
        modTensorAct A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1)) =
      (α_ A (symPow A M'.X (p + 1))
          (symPow A M.X (q + 2))).inv ≫
        ((β_ A (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 2)) ≫
        (α_ (symPow A M'.X (p + 1)) A
          (symPow A M.X (q + 2))).hom ≫
        (symPow A M'.X (p + 1) ◁ symPowAct A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1)) :=
    whiskerLeft_modTensorπ_act_snd A _ _
  refine (cancel_epi ((A ⊗ M.X) ◁
    modTensorπ A (symPowMod A M'.X p)
      (symPowMod A M.X q))).mp ?_
  -- The action side reduces through the crossing helper.
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker l1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (whiskerLeft_π_chainInsQ A M M' p q)) ?_
  refine Eq.trans (letter_cross_snd_aux
    (V := symPow A M'.X (p + 1)) (actLeft A M.X)
    (symInsL A M.X q) (symPowAct A M.X (q + 1))
    (modTensorπ A (symPowMod A M'.X p)
      (symPowMod A M.X (q + 1))) hf) ?_
  -- The insertion side reduces to the same normal form.
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker r1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (congrArg (fun t : M.X ⊗
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1)) ⟶
        chainStage2 A M M' p (q + 1) => A ◁ t)
      (whiskerLeft_π_chainInsQ A M M' p q)) _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    ((MonoidalCategory.whiskerLeft_comp _ _ _).trans
      (whisker_eq _
        ((MonoidalCategory.whiskerLeft_comp _ _ _).trans
          (whisker_eq _
            ((MonoidalCategory.whiskerLeft_comp _ _ _).trans
              (whisker_eq _
                (MonoidalCategory.whiskerLeft_comp
                  _ _ _))))))) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (Category.assoc _ _ _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (whisker_eq _ (Category.assoc _ _ _))))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (whisker_eq _ (whisker_eq _ r4))))) ?_
  rfl

/-- **The module entry is linear over the base**: the action on
the module followed by the entry is the entry followed by the
stage action. -/
theorem chainSeedQ_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    actLeft A M.X ≫ chainSeedQ A M M' d =
      (A ◁ chainSeedQ A M M' d) ≫
        modTensorAct A (symPowMod A M'.X 0) (symPowMod A M.X 1) := by
  have hsplit : chainSeedQ A M M' d =
      (ρ_ M.X).inv ≫
        MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainInsQ A M M' 0 0 := rfl
  have h1 : actLeft A M.X ≫ (ρ_ M.X).inv =
      (ρ_ (A ⊗ M.X)).inv ≫ (actLeft A M.X ▷ 𝟙_ D) :=
    rightUnitor_inv_naturality _
  have h2 : (actLeft A M.X ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) =
      MonoidalCategory.whiskerLeft (A ⊗ M.X)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        (actLeft A M.X ▷ chainStage2 A M M' 0 0) :=
    (whisker_exchange _ _).symm
  have h3 : (actLeft A M.X ▷ chainStage2 A M M' 0 0) ≫
      chainInsQ A M M' 0 0 =
      (α_ A M.X (chainStage2 A M M' 0 0)).hom ≫
        (A ◁ chainInsQ A M M' 0 0) ≫
        modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 1) :=
    chainInsQ_actLetter A M M' 0 0
  have h4 : MonoidalCategory.whiskerLeft (A ⊗ M.X)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (α_ A M.X (chainStage2 A M M' 0 0)).hom =
      (α_ A M.X (𝟙_ D)).hom ≫
        (A ◁ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) :=
    associator_naturality_right _ _ _
  have h5 : (ρ_ (A ⊗ M.X)).inv ≫ (α_ A M.X (𝟙_ D)).hom =
      A ◁ (ρ_ M.X).inv := by
    monoidal
  refine Eq.trans (whisker_eq _ hsplit) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker h1 _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker h2 _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ h3)) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker h4 _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker h5 _) ?_
  refine Eq.symm ?_
  refine Eq.trans (eq_whisker
    (congrArg (fun t : M.X ⟶ chainStage2 A M M' 0 1 =>
      A ◁ t) hsplit) _) ?_
  refine Eq.trans (eq_whisker
    ((MonoidalCategory.whiskerLeft_comp _ _ _).trans
      (whisker_eq _
        (MonoidalCategory.whiskerLeft_comp _ _ _))) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (Category.assoc _ _ _)

/-! ## The pair product of the entries -/

section PairMul

/-- Whiskered map into a tensored pair, absorbed on the left. -/
private theorem whiskerR_tensor [Category.{v} D] [MonoidalCategory D]
    {W X Y P Q : D} (f : W ⟶ X) (g : X ⟶ P) (h : Y ⟶ Q) :
    (f ▷ Y) ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  rw [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp]

/-- Whiskered map into a tensored pair, absorbed on the right. -/
private theorem whiskerL_tensor [Category.{v} D] [MonoidalCategory D]
    {W X Y P Q : D} (f : W ⟶ X) (g : Y ⟶ P) (h : X ⟶ Q) :
    (Y ◁ f) ≫ (g ⊗ₘ h) = g ⊗ₘ (f ≫ h) := by
  rw [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp]

/-- A tensored pair followed by a first-slot whisker. -/
private theorem tensor_whiskerR [Category.{v} D] [MonoidalCategory D]
    {W X Y P Q : D} (g : W ⟶ X) (k : X ⟶ P) (h : Y ⟶ Q) :
    (g ⊗ₘ h) ≫ (k ▷ Q) = (g ≫ k) ⊗ₘ h := by
  rw [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id]

/-- A tensored pair followed by a second-slot whisker. -/
private theorem tensor_whiskerL [Category.{v} D] [MonoidalCategory D]
    {W X Y P Q : D} (g : W ⟶ X) (h : Y ⟶ P) (k : P ⟶ Q) :
    (g ⊗ₘ h) ≫ (X ◁ k) = g ⊗ₘ (h ≫ k) := by
  rw [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id]

/-- **The raw pair product**: both entries enter and multiply
into the diagonal stage two levels up. -/
noncomputable def chainPairRaw
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') : M.X ⊗ M'.X ⟶
    chainStage2 A M M' 2 2 :=
  (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
    chainMul2 A M M' 0 1 1 0

/-- The common normal form of the two balance legs: the base
strand braids out front and acts after the raw pair product. -/
private noncomputable def pairOmega
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') : (M.X ⊗ A) ⊗ M'.X ⟶
    chainStage2 A M M' 2 2 :=
  ((β_ M.X A).hom ▷ M'.X) ≫ (α_ A M.X M'.X).hom ≫
    (A ◁ chainPairRaw A M M' d) ≫
    modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
      (symPowMod A M.X (1 + 1 + 0))

/-- The associator carries the whiskered entries onto the
whiskered pair. -/
private theorem pair_assoc_nat
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ((A ◁ chainSeedQ A M M' d) ⊗ₘ chainSeedP A M M' d) ≫
        (α_ A (chainStage2 A M M' 0 1) (chainStage2 A M M' 1 0)).hom =
      (α_ A M.X M'.X).hom ≫
        (A ◁ (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d)) := by
  have h := associator_naturality (𝟙 A) (chainSeedQ A M M' d)
    (chainSeedP A M M' d)
  simp only [MonoidalCategory.id_tensorHom] at h
  exact h

/-- **The first balance leg reaches the normal form.** -/
private theorem legM_pairRaw
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    modTensorLegM A M M' ≫ chainPairRaw A M M' d =
      pairOmega A M M' d := by
  have h2 : (actLeft A M.X ▷ M'.X) ≫
      (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) =
    ((A ◁ chainSeedQ A M M' d) ⊗ₘ chainSeedP A M M' d) ≫
      (modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 1) ▷
        modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) :=
    (whiskerR_tensor _ _ _).trans
      ((congrArg (fun t => t ⊗ₘ chainSeedP A M M' d)
        (chainSeedQ_linear A M M' d)).trans
        (tensor_whiskerR _ _ _).symm)
  have hE1 : modTensorLegM A M M' ≫ chainPairRaw A M M' d =
      (((β_ M.X A).hom ≫ actLeft A M.X) ▷ M'.X) ≫
        ((chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
          chainMul2 A M M' 0 1 1 0) := rfl
  have hE2 : (((β_ M.X A).hom ≫ actLeft A M.X) ▷ M'.X) ≫
      ((chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
        chainMul2 A M M' 0 1 1 0) =
    ((β_ M.X A).hom ▷ M'.X) ≫ ((actLeft A M.X ▷ M'.X) ≫
      ((chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
        chainMul2 A M M' 0 1 1 0)) :=
    (eq_whisker (MonoidalCategory.comp_whiskerRight
      (β_ M.X A).hom (actLeft A M.X) M'.X) _).trans
      (Category.assoc _ _ _)
  have hE3 : (actLeft A M.X ▷ M'.X) ≫
      ((chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
        chainMul2 A M M' 0 1 1 0) =
    ((A ◁ chainSeedQ A M M' d) ⊗ₘ chainSeedP A M M' d) ≫
      ((modTensorAct A (symPowMod A M'.X 0)
          (symPowMod A M.X 1) ▷
        modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) ≫
        chainMul2 A M M' 0 1 1 0) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker h2 _).trans (Category.assoc _ _ _))
  have hE4 : (modTensorAct A (symPowMod A M'.X 0)
      (symPowMod A M.X 1) ▷
      modTensor A (symPowMod A M'.X 1)
        (symPowMod A M.X 0)) ≫
      chainMul2 A M M' 0 1 1 0 =
    (α_ A (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1))
        (modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0))).hom ≫
      (A ◁ chainMul2 A M M' 0 1 1 0) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0)) :=
    chainMul2_actLeft A M M' 0 1 1 0
  have hE5 : ((A ◁ chainSeedQ A M M' d) ⊗ₘ
      chainSeedP A M M' d) ≫
      ((α_ A (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1))
          (modTensor A (symPowMod A M'.X 1)
            (symPowMod A M.X 0))).hom ≫
        (A ◁ chainMul2 A M M' 0 1 1 0) ≫
        modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
          (symPowMod A M.X (1 + 1 + 0))) =
    (α_ A M.X M'.X).hom ≫
      ((A ◁ (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d)) ≫
        ((A ◁ chainMul2 A M M' 0 1 1 0) ≫
          modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
            (symPowMod A M.X (1 + 1 + 0)))) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (pair_assoc_nat A M M' d) _).trans
        (Category.assoc _ _ _))
  have hE6 : (A ◁ (chainSeedQ A M M' d ⊗ₘ
      chainSeedP A M M' d)) ≫
      ((A ◁ chainMul2 A M M' 0 1 1 0) ≫
        modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
          (symPowMod A M.X (1 + 1 + 0))) =
    (A ◁ chainPairRaw A M M' d) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0)) :=
    (Category.assoc _ _ _).symm.trans
      (eq_whisker
        (MonoidalCategory.whiskerLeft_comp A
          (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d)
          (chainMul2 A M M' 0 1 1 0)).symm _)
  exact hE1.trans (hE2.trans (whisker_eq _
    (hE3.trans ((whisker_eq _ hE4).trans
      (hE5.trans (whisker_eq _ hE6))))))

/-- The inverse associator carries the pair onto the whiskered
entries. -/
private theorem rpair_assoc_nat
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (chainSeedQ A M M' d ⊗ₘ (A ◁ chainSeedP A M M' d)) ≫
        (α_ (chainStage2 A M M' 0 1) A
          (chainStage2 A M M' 1 0)).inv =
      (α_ M.X A M'.X).inv ≫
        ((chainSeedQ A M M' d ▷ A) ⊗ₘ
          chainSeedP A M M' d) := by
  have h := associator_inv_naturality (chainSeedQ A M M' d)
    (𝟙 A) (chainSeedP A M M' d)
  simp only [MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id] at h
  exact h

/-- **The second balance leg reaches the normal form.** -/
private theorem legN_pairRaw
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    modTensorLegN A M M' ≫ chainPairRaw A M M' d =
      pairOmega A M M' d := by
  have h2 : (M.X ◁ actLeft A M'.X) ≫
      (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) =
    (chainSeedQ A M M' d ⊗ₘ (A ◁ chainSeedP A M M' d)) ≫
      (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1) ◁
        modTensorAct A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) :=
    (whiskerL_tensor _ _ _).trans
      ((congrArg (fun t => chainSeedQ A M M' d ⊗ₘ t)
        (chainSeedP_linear A M M' d)).trans
        (tensor_whiskerL _ _ _).symm)
  have h6 : ((chainSeedQ A M M' d ▷ A) ⊗ₘ
      chainSeedP A M M' d) ≫
      ((β_ (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1)) A).hom ▷
        modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) =
    ((β_ M.X A).hom ▷ M'.X) ≫
      ((A ◁ chainSeedQ A M M' d) ⊗ₘ
        chainSeedP A M M' d) :=
    (tensor_whiskerR _ _ _).trans
      ((congrArg (fun t => t ⊗ₘ chainSeedP A M M' d)
        (BraidedCategory.braiding_naturality_left
          (chainSeedQ A M M' d) A)).trans
        (whiskerR_tensor _ _ _).symm)
  have hE3 : (M.X ◁ actLeft A M'.X) ≫
      ((chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d) ≫
        chainMul2 A M M' 0 1 1 0) =
    (chainSeedQ A M M' d ⊗ₘ (A ◁ chainSeedP A M M' d)) ≫
      ((modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1) ◁
        modTensorAct A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) ≫
        chainMul2 A M M' 0 1 1 0) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker h2 _).trans (Category.assoc _ _ _))
  have hE4 : (modTensor A (symPowMod A M'.X 0)
      (symPowMod A M.X 1) ◁
      modTensorAct A (symPowMod A M'.X 1)
        (symPowMod A M.X 0)) ≫
      chainMul2 A M M' 0 1 1 0 =
    (α_ (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1)) A
        (modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0))).inv ≫
      ((β_ (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1)) A).hom ▷
        modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) ≫
      (α_ A (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1))
        (modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0))).hom ≫
      (A ◁ chainMul2 A M M' 0 1 1 0) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0)) :=
    chainMul2_actMid A M M' 0 1 1 0
  have hE5 : (chainSeedQ A M M' d ⊗ₘ
      (A ◁ chainSeedP A M M' d)) ≫
      ((α_ (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1)) A
          (modTensor A (symPowMod A M'.X 1)
            (symPowMod A M.X 0))).inv ≫
        ((β_ (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1)) A).hom ▷
          modTensor A (symPowMod A M'.X 1)
            (symPowMod A M.X 0)) ≫
        (α_ A (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1))
          (modTensor A (symPowMod A M'.X 1)
            (symPowMod A M.X 0))).hom ≫
        (A ◁ chainMul2 A M M' 0 1 1 0) ≫
        modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
          (symPowMod A M.X (1 + 1 + 0))) =
    (α_ M.X A M'.X).inv ≫
      (((chainSeedQ A M M' d ▷ A) ⊗ₘ
        chainSeedP A M M' d) ≫
        (((β_ (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1)) A).hom ▷
          modTensor A (symPowMod A M'.X 1)
            (symPowMod A M.X 0)) ≫
        (α_ A (modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 1))
          (modTensor A (symPowMod A M'.X 1)
            (symPowMod A M.X 0))).hom ≫
        (A ◁ chainMul2 A M M' 0 1 1 0) ≫
        modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
          (symPowMod A M.X (1 + 1 + 0)))) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (rpair_assoc_nat A M M' d) _).trans
        (Category.assoc _ _ _))
  have hE6 : ((chainSeedQ A M M' d ▷ A) ⊗ₘ
      chainSeedP A M M' d) ≫
      (((β_ (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1)) A).hom ▷
        modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0)) ≫
      (α_ A (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1))
        (modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0))).hom ≫
      (A ◁ chainMul2 A M M' 0 1 1 0) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0))) =
    ((β_ M.X A).hom ▷ M'.X) ≫
      (((A ◁ chainSeedQ A M M' d) ⊗ₘ
        chainSeedP A M M' d) ≫
      ((α_ A (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1))
        (modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0))).hom ≫
      (A ◁ chainMul2 A M M' 0 1 1 0) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0)))) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (h6) _).trans (Category.assoc _ _ _))
  have hE7 : ((A ◁ chainSeedQ A M M' d) ⊗ₘ
      chainSeedP A M M' d) ≫
      ((α_ A (modTensor A (symPowMod A M'.X 0)
        (symPowMod A M.X 1))
        (modTensor A (symPowMod A M'.X 1)
          (symPowMod A M.X 0))).hom ≫
      (A ◁ chainMul2 A M M' 0 1 1 0) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0))) =
    (α_ A M.X M'.X).hom ≫
      ((A ◁ (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d)) ≫
        ((A ◁ chainMul2 A M M' 0 1 1 0) ≫
          modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
            (symPowMod A M.X (1 + 1 + 0)))) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (pair_assoc_nat A M M' d) _).trans
        (Category.assoc _ _ _))
  have hE8 : (A ◁ (chainSeedQ A M M' d ⊗ₘ
      chainSeedP A M M' d)) ≫
      ((A ◁ chainMul2 A M M' 0 1 1 0) ≫
        modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
          (symPowMod A M.X (1 + 1 + 0))) =
    (A ◁ chainPairRaw A M M' d) ≫
      modTensorAct A (symPowMod A M'.X (0 + 1 + 1))
        (symPowMod A M.X (1 + 1 + 0)) :=
    (Category.assoc _ _ _).symm.trans
      (eq_whisker
        (MonoidalCategory.whiskerLeft_comp A
          (chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d)
          (chainMul2 A M M' 0 1 1 0)).symm _)
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (hE3.trans ((whisker_eq _ hE4).trans
    hE5))).trans ?_
  refine (Iso.hom_inv_id_assoc _ _).trans ?_
  exact hE6.trans (whisker_eq _ (hE7.trans
    (whisker_eq _ hE8)))

/-- The two balance legs agree. -/
theorem chainPair_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    modTensorLegM A M M' ≫ chainPairRaw A M M' d =
      modTensorLegN A M M' ≫ chainPairRaw A M M' d :=
  (legM_pairRaw A M M' d).trans (legN_pairRaw A M M' d).symm

/-- **The pair product of the entries**, descended to the
relative tensor product. -/
noncomputable def chainPairMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') : modTensor A M M' ⟶
    chainStage2 A M M' 2 2 :=
  modTensorDesc A M M' (chainPairRaw A M M' d)
    (chainPair_cond A M M' d)

/-- Defining equation of the descended pair product. -/
@[reassoc]
theorem modTensorπ_chainPairMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    modTensorπ A M M' ≫ chainPairMul A M M' d =
      chainPairRaw A M M' d :=
  modTensorπ_desc A M M' _ _

/-- The insertion at the bottom, cast-free. -/
private theorem symInsL_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X] :
    symInsL A X 0 =
      ((symPowOne A X).inv ▷ symPow A X 1) ≫
        symMul A X 1 1 := by
  rw [symInsL,
    show symPowCast A X (by omega : 1 + (0 + 1) = 0 + 2) =
      𝟙 (symPow A X (0 + 2)) from rfl, Category.comp_id]

private theorem pairIns_leftCover [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    ((M'.X ⊗ M.X) ◁ modTensorπ A
      (symPowMod A M'.X 0) (symPowMod A M.X 0)) ≫
      ((((symPowOne A M'.X).inv ⊗ₘ
        (symPowOne A M.X).inv) ≫
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ▷
        chainStage2 A M M' 0 0) ≫
      chainMul2 A M M' 0 0 0 0 =
    tensorμ M'.X M.X (symPow A M'.X 1) (symPow A M.X 1) ≫
      (symInsL A M'.X 0 ⊗ₘ symInsL A M.X 0) ≫
      modTensorπ A (symPowMod A M'.X 1)
        (symPowMod A M.X 1) := by
  have hL1 : ((M'.X ⊗ M.X) ◁
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)) ≫
      ((((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ≫
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ▷ chainStage2 A M M' 0 0) =
    ((((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ≫
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ▷
      (symPow A M'.X 1 ⊗ symPow A M.X 1)) ≫
      ((modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ◁
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) :=
    whisker_exchange _ _
  have hL2 : ((((symPowOne A M'.X).inv ⊗ₘ
      (symPowOne A M.X).inv) ≫
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)) ▷
      (symPow A M'.X 1 ⊗ symPow A M.X 1)) ≫
      ((modTensor A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ◁
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) =
    (((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ▷
      (symPow A M'.X 1 ⊗ symPow A M.X 1)) ≫
      (modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0) ⊗ₘ
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) := by
    erw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      ← MonoidalCategory.tensorHom_def]
  have hL3 : (modTensorπ A (symPowMod A M'.X 0)
      (symPowMod A M.X 0) ⊗ₘ
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)) ≫
      chainMul2 A M M' 0 0 0 0 =
    tensorμ (symPow A M'.X 1) (symPow A M.X 1)
        (symPow A M'.X 1) (symPow A M.X 1) ≫
      (symMul A M'.X 1 1 ⊗ₘ symMul A M.X 1 1) ≫
      modTensorπ A (symPowMod A M'.X 1)
        (symPowMod A M.X 1) :=
    tensorHom_π_chainMul2 A M M' 0 0 0 0
  have hL4 : (((symPowOne A M'.X).inv ⊗ₘ
      (symPowOne A M.X).inv) ▷
      (symPow A M'.X 1 ⊗ symPow A M.X 1)) ≫
      tensorμ (symPow A M'.X 1) (symPow A M.X 1)
        (symPow A M'.X 1) (symPow A M.X 1) =
    tensorμ M'.X M.X (symPow A M'.X 1) (symPow A M.X 1) ≫
      (((symPowOne A M'.X).inv ▷ symPow A M'.X 1) ⊗ₘ
        ((symPowOne A M.X).inv ▷ symPow A M.X 1)) := by
    have h := tensorμ_natural (symPowOne A M'.X).inv
      (symPowOne A M.X).inv (𝟙 (symPow A M'.X 1))
      (𝟙 (symPow A M.X 1))
    simp only [MonoidalCategory.tensorHom_id] at h
    simpa using h
  -- Right side: naturality of the associator, the two insertion
  -- defining equations, and the rearrangement identifying the
  -- crossing with the interchange.
  have hIns : ((symPowOne A M'.X).inv ▷ symPow A M'.X 1) ≫
        symMul A M'.X 1 1 = symInsL A M'.X 0 :=
    (symInsL_zero A M'.X).symm
  have hIns' : ((symPowOne A M.X).inv ▷ symPow A M.X 1) ≫
        symMul A M.X 1 1 = symInsL A M.X 0 :=
    (symInsL_zero A M.X).symm
  have hMuls : (((symPowOne A M'.X).inv ▷ symPow A M'.X 1) ⊗ₘ
      ((symPowOne A M.X).inv ▷ symPow A M.X 1)) ≫
      (symMul A M'.X 1 1 ⊗ₘ symMul A M.X 1 1) =
    symInsL A M'.X 0 ⊗ₘ symInsL A M.X 0 :=
    (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (· ⊗ₘ ·) hIns hIns')
  have hLfinal : ((M'.X ⊗ M.X) ◁ modTensorπ A
      (symPowMod A M'.X 0) (symPowMod A M.X 0)) ≫
      ((((symPowOne A M'.X).inv ⊗ₘ
        (symPowOne A M.X).inv) ≫
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ▷
        chainStage2 A M M' 0 0) ≫
      chainMul2 A M M' 0 0 0 0 =
    tensorμ M'.X M.X (symPow A M'.X 1) (symPow A M.X 1) ≫
      (symInsL A M'.X 0 ⊗ₘ symInsL A M.X 0) ≫
      modTensorπ A (symPowMod A M'.X 1)
        (symPowMod A M.X 1) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker hL1 _).trans ?_
    refine (eq_whisker hL2 _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (whisker_eq _ hL3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker hL4 _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine whisker_eq _ ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact eq_whisker hMuls _
  exact hLfinal

/-- **Pair multiplication is double insertion**: multiplying the
embedded letter pair onto a bottom-stage element inserts the two
letters. -/
theorem pairIns [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    ((((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ≫
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ▷ chainStage2 A M M' 0 0) ≫
      chainMul2 A M M' 0 0 0 0 =
    (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ chainInsQ A M M' 0 0) ≫
      chainInsP A M M' 0 1 := by
  refine (cancel_epi ((M'.X ⊗ M.X) ◁
    modTensorπ A (symPowMod A M'.X 0)
      (symPowMod A M.X 0))).mp ?_
  -- Left side: exchange the cover, pair the projections, expand
  -- the multiplication, and slide the singleton maps through the
  -- interchange.
  have hR1 : ((M'.X ⊗ M.X) ◁
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom =
    (α_ M'.X M.X (symPow A M'.X 1 ⊗ symPow A M.X 1)).hom ≫
      (M'.X ◁ (M.X ◁ modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0))) :=
    associator_naturality_right _ _ _
  have hR2 : (M'.X ◁ (M.X ◁ modTensorπ A
      (symPowMod A M'.X 0) (symPowMod A M.X 0))) ≫
      (M'.X ◁ chainInsQ A M M' 0 0) =
    M'.X ◁ ((α_ M.X (symPow A M'.X 1)
        (symPow A M.X 1)).inv ≫
      ((β_ M.X (symPow A M'.X 1)).hom ▷ symPow A M.X 1) ≫
      (α_ (symPow A M'.X 1) M.X (symPow A M.X 1)).hom ≫
      (symPow A M'.X 1 ◁ symInsL A M.X 0) ≫
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 1)) :=
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
      (congrArg (fun t => M'.X ◁ t)
        (whiskerLeft_π_chainInsQ A M M' 0 0))
  have hR3 : (M'.X ◁ modTensorπ A (symPowMod A M'.X 0)
      (symPowMod A M.X 1)) ≫ chainInsP A M M' 0 1 =
    (α_ M'.X (symPow A M'.X 1) (symPow A M.X 2)).inv ≫
      (symInsL A M'.X 0 ▷ symPow A M.X 2) ≫
      modTensorπ A (symPowMod A M'.X 1)
        (symPowMod A M.X 1) :=
    whiskerLeft_π_chainInsP A M M' 0 1
  have hR4 : (M'.X ◁ (symPow A M'.X 1 ◁
      symInsL A M.X 0)) ≫
      (α_ M'.X (symPow A M'.X 1) (symPow A M.X 2)).inv =
    (α_ M'.X (symPow A M'.X 1)
        (M.X ⊗ symPow A M.X 1)).inv ≫
      ((M'.X ⊗ symPow A M'.X 1) ◁ symInsL A M.X 0) :=
    associator_inv_naturality_right _ _ _
  have hR5 : ((M'.X ⊗ symPow A M'.X 1) ◁
      symInsL A M.X 0) ≫
      (symInsL A M'.X 0 ▷ symPow A M.X 2) =
    (symInsL A M'.X 0 ▷ (M.X ⊗ symPow A M.X 1)) ≫
      (symPow A M'.X (0 + 2) ◁ symInsL A M.X 0) :=
    whisker_exchange _ _
  have hR7 : (α_ M'.X M.X (symPow A M'.X 1 ⊗
      symPow A M.X 1)).hom ≫
      (M'.X ◁ (α_ M.X (symPow A M'.X 1)
        (symPow A M.X 1)).inv) ≫
      (M'.X ◁ ((β_ M.X (symPow A M'.X 1)).hom ▷
        symPow A M.X 1)) ≫
      (M'.X ◁ (α_ (symPow A M'.X 1) M.X
        (symPow A M.X 1)).hom) ≫
      (α_ M'.X (symPow A M'.X 1)
        (M.X ⊗ symPow A M.X 1)).inv =
    tensorμ M'.X M.X (symPow A M'.X 1) (symPow A M.X 1) :=
    rfl
  have hR8 : (symInsL A M'.X 0 ▷ (M.X ⊗ symPow A M.X 1)) ≫
      (symPow A M'.X (0 + 2) ◁ symInsL A M.X 0) =
    symInsL A M'.X 0 ⊗ₘ symInsL A M.X 0 :=
    (MonoidalCategory.tensorHom_def _ _).symm
  -- Assemble both sides at the common form
  -- tensorμ ≫ (symInsL ⊗ symInsL) ≫ π.
  have hLfinal := pairIns_leftCover A M M'
  have hexp : M'.X ◁ ((α_ M.X (symPow A M'.X 1)
      (symPow A M.X 1)).inv ≫
      ((β_ M.X (symPow A M'.X 1)).hom ▷ symPow A M.X 1) ≫
      (α_ (symPow A M'.X 1) M.X (symPow A M.X 1)).hom ≫
      (symPow A M'.X 1 ◁ symInsL A M.X 0) ≫
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 1)) =
    (M'.X ◁ (α_ M.X (symPow A M'.X 1)
      (symPow A M.X 1)).inv) ≫
    (M'.X ◁ ((β_ M.X (symPow A M'.X 1)).hom ▷
      symPow A M.X 1)) ≫
    (M'.X ◁ (α_ (symPow A M'.X 1) M.X
      (symPow A M.X 1)).hom) ≫
    (M'.X ◁ (symPow A M'.X 1 ◁ symInsL A M.X 0)) ≫
    (M'.X ◁ modTensorπ A (symPowMod A M'.X 0)
      (symPowMod A M.X 1)) := by
    repeat' erw [MonoidalCategory.whiskerLeft_comp]
  have hRfinal : ((M'.X ⊗ M.X) ◁ modTensorπ A
      (symPowMod A M'.X 0) (symPowMod A M.X 0)) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ chainInsQ A M M' 0 0) ≫
      chainInsP A M M' 0 1 =
    tensorμ M'.X M.X (symPow A M'.X 1) (symPow A M.X 1) ≫
      (symInsL A M'.X 0 ⊗ₘ symInsL A M.X 0) ≫
      modTensorπ A (symPowMod A M'.X 1)
        (symPowMod A M.X 1) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker hR1 _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (whisker_eq _ ((Category.assoc _ _ _).symm.trans
      ((eq_whisker hR2 _).trans
        (eq_whisker hexp _)))).trans ?_
    -- peel the five whiskers
    refine (whisker_eq _ (by
      repeat' erw [Category.assoc] :
        ((M'.X ◁ (α_ M.X (symPow A M'.X 1)
            (symPow A M.X 1)).inv) ≫
          (M'.X ◁ ((β_ M.X (symPow A M'.X 1)).hom ▷
            symPow A M.X 1)) ≫
          (M'.X ◁ (α_ (symPow A M'.X 1) M.X
            (symPow A M.X 1)).hom) ≫
          (M'.X ◁ (symPow A M'.X 1 ◁ symInsL A M.X 0)) ≫
          (M'.X ◁ modTensorπ A (symPowMod A M'.X 0)
            (symPowMod A M.X 1))) ≫
          chainInsP A M M' 0 1 =
        (M'.X ◁ (α_ M.X (symPow A M'.X 1)
            (symPow A M.X 1)).inv) ≫
          (M'.X ◁ ((β_ M.X (symPow A M'.X 1)).hom ▷
            symPow A M.X 1)) ≫
          (M'.X ◁ (α_ (symPow A M'.X 1) M.X
            (symPow A M.X 1)).hom) ≫
          (M'.X ◁ (symPow A M'.X 1 ◁ symInsL A M.X 0)) ≫
          ((M'.X ◁ modTensorπ A (symPowMod A M'.X 0)
            (symPowMod A M.X 1)) ≫
            chainInsP A M M' 0 1))).trans ?_
    refine (whisker_eq _ (whisker_eq _ (whisker_eq _
      (whisker_eq _ (whisker_eq _ hR3))))).trans ?_
    refine (whisker_eq _ (whisker_eq _ (whisker_eq _
      (whisker_eq _ ((Category.assoc _ _ _).symm.trans
        ((eq_whisker hR4 _).trans
          (Category.assoc _ _ _))))))).trans ?_
    refine (whisker_eq _ (whisker_eq _ (whisker_eq _
      (whisker_eq _ (whisker_eq _
        ((Category.assoc _ _ _).symm.trans
          ((eq_whisker hR5 _).trans
            (Category.assoc _ _ _)))))))).trans ?_
    refine ((by simp only [Category.assoc] :
      (α_ M'.X M.X (symPow A M'.X 1 ⊗
          symPow A M.X 1)).hom ≫
        (M'.X ◁ (α_ M.X (symPow A M'.X 1)
          (symPow A M.X 1)).inv) ≫
        (M'.X ◁ ((β_ M.X (symPow A M'.X 1)).hom ▷
          symPow A M.X 1)) ≫
        (M'.X ◁ (α_ (symPow A M'.X 1) M.X
          (symPow A M.X 1)).hom) ≫
        (α_ M'.X (symPow A M'.X 1)
          (M.X ⊗ symPow A M.X 1)).inv ≫
        (symInsL A M'.X 0 ▷ (M.X ⊗ symPow A M.X 1)) ≫
        (symPow A M'.X (0 + 2) ◁ symInsL A M.X 0) ≫
        modTensorπ A (symPowMod A M'.X 1)
          (symPowMod A M.X 1) =
      ((α_ M'.X M.X (symPow A M'.X 1 ⊗
          symPow A M.X 1)).hom ≫
        (M'.X ◁ (α_ M.X (symPow A M'.X 1)
          (symPow A M.X 1)).inv) ≫
        (M'.X ◁ ((β_ M.X (symPow A M'.X 1)).hom ▷
          symPow A M.X 1)) ≫
        (M'.X ◁ (α_ (symPow A M'.X 1) M.X
          (symPow A M.X 1)).hom) ≫
        (α_ M'.X (symPow A M'.X 1)
          (M.X ⊗ symPow A M.X 1)).inv) ≫
        (symInsL A M'.X 0 ▷ (M.X ⊗ symPow A M.X 1)) ≫
        (symPow A M'.X (0 + 2) ◁ symInsL A M.X 0) ≫
        modTensorπ A (symPowMod A M'.X 1)
          (symPowMod A M.X 1))).trans ?_
    refine (eq_whisker hR7 _).trans ?_
    refine whisker_eq _ ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact eq_whisker hR8 _
  exact hLfinal.trans hRfinal.symm

/-- The first-slot insertion against the multiplication, solved
for the whiskered form. -/
private theorem insP_solved
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    (chainInsP A M M' 0 0 ▷ chainStage2 A M M' 0 1) ≫
        chainMul2 A M M' (0 + 1) 0 0 1 =
      (α_ M'.X (chainStage2 A M M' 0 0) (chainStage2 A M M' 0 1)).hom ≫
      (M'.X ◁ chainMul2 A M M' 0 0 0 1) ≫
      chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
  have h := chainInsP_mul A M M' 0 0 0 1
  rw [show chainStage2Cast A M M'
      (by omega : 0 + 1 + 1 + 0 = 0 + 1 + 0 + 1)
      (by omega : 0 + 1 + 1 = 0 + 1 + 1) =
    𝟙 (chainStage2 A M M' (0 + 1 + 0 + 1) (0 + 1 + 1)) from
      rfl, Category.comp_id] at h
  rw [h, Iso.hom_inv_id_assoc]

/-- The second-slot insertion against the multiplication, solved
for the whiskered form. -/
private theorem insQ_solved
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    (chainInsQ A M M' 0 0 ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' 0 (0 + 1) 0 0 =
      (α_ M.X (chainStage2 A M M' 0 0) (chainStage2 A M M' 0 0)).hom ≫
      (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
      chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0) := by
  have h := chainInsQ_mul A M M' 0 0 0 0
  rw [show chainStage2Cast A M M'
      (by omega : 0 + 1 + 0 = 0 + 1 + 0)
      (by omega : 0 + 1 + 1 + 0 = 0 + 1 + 0 + 1) =
    𝟙 (chainStage2 A M M' (0 + 1 + 0) (0 + 1 + 0 + 1)) from
      rfl, Category.comp_id] at h
  rw [h, Iso.hom_inv_id_assoc]

/-- The multiplication with the first-slot insertion in its
second factor: braid, insert, multiply. -/
private theorem insP_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    (chainStage2 A M M' 0 1 ◁ chainInsP A M M' 0 0) ≫
        chainMul2 A M M' 0 1 1 0 =
      (β_ (chainStage2 A M M' 0 1) (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (α_ M'.X (chainStage2 A M M' 0 0) (chainStage2 A M M' 0 1)).hom ≫
      (M'.X ◁ chainMul2 A M M' 0 0 0 1) ≫
      chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
  have hcomm : chainMul2 A M M' 0 1 1 0 =
      (β_ (chainStage2 A M M' 0 1)
        (chainStage2 A M M' 1 0)).hom ≫
      chainMul2 A M M' 1 0 0 1 ≫
      chainStage2Cast A M M'
        (by omega : 1 + 1 + 0 = 0 + 1 + 1)
        (by omega : 0 + 1 + 1 = 1 + 1 + 0) :=
    (chainMul2_comm A M M' 0 1 1 0).symm
  rw [show chainStage2Cast A M M'
      (by omega : 1 + 1 + 0 = 0 + 1 + 1)
      (by omega : 0 + 1 + 1 = 1 + 1 + 0) =
    𝟙 (chainStage2 A M M' (0 + 1 + 1) (1 + 1 + 0)) from
      rfl, Category.comp_id] at hcomm
  have hnat : (chainStage2 A M M' 0 1 ◁
      chainInsP A M M' 0 0) ≫
      (β_ (chainStage2 A M M' 0 1)
        (chainStage2 A M M' 1 0)).hom =
    (β_ (chainStage2 A M M' 0 1)
      (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (chainInsP A M M' 0 0 ▷ chainStage2 A M M' 0 1) :=
    BraidedCategory.braiding_naturality_right _ _
  calc (chainStage2 A M M' 0 1 ◁ chainInsP A M M' 0 0) ≫
      chainMul2 A M M' 0 1 1 0
      = (chainStage2 A M M' 0 1 ◁ chainInsP A M M' 0 0) ≫
          (β_ (chainStage2 A M M' 0 1)
            (chainStage2 A M M' 1 0)).hom ≫
          chainMul2 A M M' 1 0 0 1 := by
        rw [hcomm]
    _ = (β_ (chainStage2 A M M' 0 1)
          (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          ((chainInsP A M M' 0 0 ▷
            chainStage2 A M M' 0 1) ≫
          chainMul2 A M M' 1 0 0 1) := by
        rw [← Category.assoc, hnat, Category.assoc]
    _ = (β_ (chainStage2 A M M' 0 1)
          (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          ((chainInsP A M M' 0 0 ▷
            chainStage2 A M M' 0 1) ≫
          chainMul2 A M M' (0 + 1) 0 0 1) := by
        rw [show chainMul2 A M M' 1 0 0 1 =
          chainMul2 A M M' (0 + 1) 0 0 1 from rfl]
    _ = (β_ (chainStage2 A M M' 0 1)
          (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          (α_ M'.X (chainStage2 A M M' 0 0)
            (chainStage2 A M M' 0 1)).hom ≫
          (M'.X ◁ chainMul2 A M M' 0 0 0 1) ≫
          chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
        rw [insP_solved]

/-- The multiplication with the second-slot insertion in its
second factor: braid, insert, multiply. -/
private theorem insQ_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A) :
    (chainStage2 A M M' 0 0 ◁ chainInsQ A M M' 0 0) ≫
        chainMul2 A M M' 0 0 0 1 =
      (β_ (chainStage2 A M M' 0 0) (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (α_ M.X (chainStage2 A M M' 0 0) (chainStage2 A M M' 0 0)).hom ≫
      (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
      chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0) := by
  have hcomm : chainMul2 A M M' 0 0 0 1 =
      (β_ (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 1)).hom ≫
      chainMul2 A M M' 0 1 0 0 ≫
      chainStage2Cast A M M'
        (by omega : 0 + 1 + 0 = 0 + 1 + 0)
        (by omega : 1 + 1 + 0 = 0 + 1 + 1) :=
    (chainMul2_comm A M M' 0 0 0 1).symm
  rw [show chainStage2Cast A M M'
      (by omega : 0 + 1 + 0 = 0 + 1 + 0)
      (by omega : 1 + 1 + 0 = 0 + 1 + 1) =
    𝟙 (chainStage2 A M M' (0 + 1 + 0) (0 + 1 + 1)) from
      rfl, Category.comp_id] at hcomm
  have hnat : (chainStage2 A M M' 0 0 ◁
      chainInsQ A M M' 0 0) ≫
      (β_ (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 1)).hom =
    (β_ (chainStage2 A M M' 0 0)
      (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (chainInsQ A M M' 0 0 ▷ chainStage2 A M M' 0 0) :=
    BraidedCategory.braiding_naturality_right _ _
  calc (chainStage2 A M M' 0 0 ◁ chainInsQ A M M' 0 0) ≫
      chainMul2 A M M' 0 0 0 1
      = (chainStage2 A M M' 0 0 ◁ chainInsQ A M M' 0 0) ≫
          (β_ (chainStage2 A M M' 0 0)
            (chainStage2 A M M' 0 1)).hom ≫
          chainMul2 A M M' 0 1 0 0 := by
        rw [hcomm]
    _ = (β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          ((chainInsQ A M M' 0 0 ▷
            chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' 0 1 0 0) := by
        rw [← Category.assoc, hnat, Category.assoc]
    _ = (β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          ((chainInsQ A M M' 0 0 ▷
            chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' 0 (0 + 1) 0 0) := by
        rw [show chainMul2 A M M' 0 1 0 0 =
          chainMul2 A M M' 0 (0 + 1) 0 0 from rfl]
    _ = (β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          (α_ M.X (chainStage2 A M M' 0 0)
            (chainStage2 A M M' 0 0)).hom ≫
          (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
          chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0) := by
        rw [insQ_solved]

/-- Any morphism into a stage followed by the transition is the
seed fed beside it. -/
private theorem comp_chainDelta2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') {W : D} (p q : ℕ)
    (f : W ⟶ chainStage2 A M M' p q) :
    f ≫ chainDelta2 A M M' d p q =
      (ρ_ W).inv ≫
        (W ◁ chainSeed A M M' d) ≫
        ((f ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p q 0 0) := by
  have h1 : f ≫ (ρ_ (chainStage2 A M M' p q)).inv =
      (ρ_ W).inv ≫ (f ▷ (𝟙_ D)) :=
    rightUnitor_inv_naturality _
  have h2 : (f ▷ (𝟙_ D)) ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) =
    (W ◁ chainSeed A M M' d) ≫
      (f ▷ chainStage2 A M M' 0 0) :=
    (whisker_exchange _ _).symm
  calc f ≫ chainDelta2 A M M' d p q
      = (f ≫ (ρ_ (chainStage2 A M M' p q)).inv) ≫
          MonoidalCategory.whiskerLeft
            (chainStage2 A M M' p q)
            (Y₂ := chainStage2 A M M' 0 0)
            (chainSeed A M M' d) ≫
          chainMul2 A M M' p q 0 0 := by
        rw [chainDelta2]
        simp only [Category.assoc]
    _ = (ρ_ W).inv ≫ ((f ▷ (𝟙_ D)) ≫
          MonoidalCategory.whiskerLeft
            (chainStage2 A M M' p q)
            (Y₂ := chainStage2 A M M' 0 0)
            (chainSeed A M M' d)) ≫
          chainMul2 A M M' p q 0 0 := by
        rw [h1]
        simp only [Category.assoc]
    _ = (ρ_ W).inv ≫
          (W ◁ chainSeed A M M' d) ≫
          ((f ▷ chainStage2 A M M' 0 0) ≫
            chainMul2 A M M' p q 0 0) := by
        rw [h2]
        repeat' erw [Category.assoc]

/-- **The raw pair product, normalised**: both letters braid to
canonical position, the seeds feed in, and the two insertions
stack. -/
private theorem pairRaw_normal
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    chainPairRaw A M M' d =
      (β_ M.X M'.X).hom ≫
      ((((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
        ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
        chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0))) ≫
      chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1)) := by
  have hW2 : chainSeedQ A M M' d ⊗ₘ chainSeedP A M M' d =
      (((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
        ((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
      (chainInsQ A M M' 0 0 ⊗ₘ chainInsP A M M' 0 0) := by
    rw [show chainSeedQ A M M' d =
        ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫ chainInsQ A M M' 0 0 from
        (Category.assoc _ _ _).symm,
      show chainSeedP A M M' d =
        ((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫ chainInsP A M M' 0 0 from
        (Category.assoc _ _ _).symm,
      MonoidalCategory.tensorHom_comp_tensorHom]
  have hW3 : (chainInsQ A M M' 0 0 ⊗ₘ
      chainInsP A M M' 0 0) ≫ chainMul2 A M M' 0 1 1 0 =
    (chainInsQ A M M' 0 0 ▷ (M'.X ⊗ chainStage2 A M M' 0 0)) ≫
      ((chainStage2 A M M' 0 1 ◁ chainInsP A M M' 0 0) ≫
        chainMul2 A M M' 0 1 1 0) :=
    (eq_whisker (MonoidalCategory.tensorHom_def _ _) _).trans
      (Category.assoc _ _ _)
  have hW5 : (chainInsQ A M M' 0 0 ▷
      (M'.X ⊗ chainStage2 A M M' 0 0)) ≫
      (β_ (chainStage2 A M M' 0 1)
        (M'.X ⊗ chainStage2 A M M' 0 0)).hom =
    (β_ (M.X ⊗ chainStage2 A M M' 0 0)
      (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      ((M'.X ⊗ chainStage2 A M M' 0 0) ◁ chainInsQ A M M' 0 0) :=
    BraidedCategory.braiding_naturality_left _ _
  have hW6 : ((M'.X ⊗ chainStage2 A M M' 0 0) ◁
      chainInsQ A M M' 0 0) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 1)).hom =
    (α_ M'.X (chainStage2 A M M' 0 0)
      (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((chainStage2 A M M' 0 0) ◁
        chainInsQ A M M' 0 0)) :=
    associator_naturality_right _ _ _
  have hW7 : (M'.X ◁ ((chainStage2 A M M' 0 0) ◁
      chainInsQ A M M' 0 0)) ≫
      (M'.X ◁ chainMul2 A M M' 0 0 0 1) =
    M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (α_ M.X (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 0)).hom ≫
      (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
      chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0)) :=
    (MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
      (congrArg (fun t => M'.X ◁ t) (insQ_snd A M M'))
  have hW8 : (((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
      (β_ (M.X ⊗ chainStage2 A M M' 0 0)
        (M'.X ⊗ chainStage2 A M M' 0 0)).hom =
    (β_ M.X M'.X).hom ≫
      (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
        ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) :=
    BraidedCategory.braiding_naturality _ _
  calc chainPairRaw A M M' d
      = (((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
          ((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
          ((chainInsQ A M M' 0 0 ⊗ₘ chainInsP A M M' 0 0) ≫
            chainMul2 A M M' 0 1 1 0) := by
        rw [chainPairRaw, hW2]
        simp only [Category.assoc]
    _ = (((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
          ((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
          (chainInsQ A M M' 0 0 ▷
            (M'.X ⊗ chainStage2 A M M' 0 0)) ≫
          ((β_ (chainStage2 A M M' 0 1)
            (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          (α_ M'.X (chainStage2 A M M' 0 0)
            (chainStage2 A M M' 0 1)).hom ≫
          (M'.X ◁ chainMul2 A M M' 0 0 0 1) ≫
          chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1)) := by
        rw [hW3, insP_snd]
    _ = (((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
          ((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
          (β_ (M.X ⊗ chainStage2 A M M' 0 0)
            (M'.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          ((M'.X ⊗ chainStage2 A M M' 0 0) ◁
            chainInsQ A M M' 0 0) ≫
          (α_ M'.X (chainStage2 A M M' 0 0)
            (chainStage2 A M M' 0 1)).hom ≫
          (M'.X ◁ chainMul2 A M M' 0 0 0 1) ≫
          chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
        rw [← Category.assoc
          (chainInsQ A M M' 0 0 ▷
            (M'.X ⊗ chainStage2 A M M' 0 0)), hW5]
        simp only [Category.assoc]
    _ = (β_ M.X M'.X).hom ≫
          (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
            ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
          ((M'.X ⊗ chainStage2 A M M' 0 0) ◁
            chainInsQ A M M' 0 0) ≫
          (α_ M'.X (chainStage2 A M M' 0 0)
            (chainStage2 A M M' 0 1)).hom ≫
          (M'.X ◁ chainMul2 A M M' 0 0 0 1) ≫
          chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
        rw [← Category.assoc _
          (β_ (M.X ⊗ chainStage2 A M M' 0 0)
            (M'.X ⊗ chainStage2 A M M' 0 0)).hom, hW8]
        simp only [Category.assoc]
    _ = (β_ M.X M'.X).hom ≫
          (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
            ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
          (α_ M'.X (chainStage2 A M M' 0 0)
            (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          ((M'.X ◁ ((chainStage2 A M M' 0 0) ◁
            chainInsQ A M M' 0 0)) ≫
          (M'.X ◁ chainMul2 A M M' 0 0 0 1)) ≫
          chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
        rw [← Category.assoc
          ((M'.X ⊗ chainStage2 A M M' 0 0) ◁
            chainInsQ A M M' 0 0), hW6]
        simp only [Category.assoc]
    _ = (β_ M.X M'.X).hom ≫
          (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ⊗ₘ
            ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d))) ≫
          (α_ M'.X (chainStage2 A M M' 0 0)
            (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
          (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
              (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
            (α_ M.X (chainStage2 A M M' 0 0)
              (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
            chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0))) ≫
          chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) := by
        rw [hW7]

/-- **The swapped base element against the double transition,
normalised**: the pair element rides the first transition into
the double insertion, and the second transition slides inside. -/
private theorem swapDelta_normal
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ((((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ≫
      modTensorπ A (symPowMod A M'.X 0) (symPowMod A M.X 0)) ≫
      chainDelta2 A M M' d 0 0) ≫ chainDelta2 A M M' d 1 1 =
    (ρ_ (M'.X ⊗ M.X)).inv ≫
      (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
        chainDelta2 A M M' d 0 0))) ≫
      (M'.X ◁ chainInsQ A M M' (0 + 1) (0 + 1)) ≫
      chainInsP A M M' (0 + 1) (1 + 1) := by
  have hU2 := comp_chainDelta2 A M M' d 0 0
    ((((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ≫
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)))
  have hU4 : chainInsP A M M' 0 1 ≫
      chainDelta2 A M M' d 1 1 =
    (M'.X ◁ chainDelta2 A M M' d 0 1) ≫
      chainInsP A M M' (0 + 1) (1 + 1) := by
    rw [show chainDelta2 A M M' d 1 1 =
      chainDelta2 A M M' d (0 + 1) 1 from rfl]
    exact (chainInsP_delta2 A M M' d 0 1).symm
  have hU5 : chainInsQ A M M' 0 0 ≫
      chainDelta2 A M M' d 0 1 =
    (M.X ◁ chainDelta2 A M M' d 0 0) ≫
      chainInsQ A M M' (0 + 1) (0 + 1) := by
    rw [show chainDelta2 A M M' d 0 1 =
      chainDelta2 A M M' d 0 (0 + 1) from rfl]
    exact (chainInsQ_delta2 A M M' d 0 0).symm
  have hU6 : ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom =
    (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ chainSeed A M M' d)) :=
    associator_naturality_right _ _ _
  have C12 : ((((symPowOne A M'.X).inv ⊗ₘ
      (symPowOne A M.X).inv) ≫
      modTensorπ A (symPowMod A M'.X 0)
        (symPowMod A M.X 0)) ≫
      chainDelta2 A M M' d 0 0) ≫ chainDelta2 A M M' d 1 1 =
    ((ρ_ (M'.X ⊗ M.X)).inv ≫
      ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      ((α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
        (M'.X ◁ chainInsQ A M M' 0 0) ≫
        chainInsP A M M' 0 1)) ≫
      chainDelta2 A M M' d 1 1 :=
    eq_whisker (hU2.trans (whisker_eq _
      (whisker_eq _ (pairIns A M M')))) _
  have C3 : ((ρ_ (M'.X ⊗ M.X)).inv ≫
      ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      ((α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
        (M'.X ◁ chainInsQ A M M' 0 0) ≫
        chainInsP A M M' 0 1)) ≫
      chainDelta2 A M M' d 1 1 =
    (ρ_ (M'.X ⊗ M.X)).inv ≫
      ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ chainInsQ A M M' 0 0) ≫
      (chainInsP A M M' 0 1 ≫
        chainDelta2 A M M' d 1 1) := by
    repeat' erw [Category.assoc]
  have C4 : (ρ_ (M'.X ⊗ M.X)).inv ≫
      ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ chainInsQ A M M' 0 0) ≫
      (chainInsP A M M' 0 1 ≫
        chainDelta2 A M M' d 1 1) =
    (ρ_ (M'.X ⊗ M.X)).inv ≫
      ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ chainInsQ A M M' 0 0) ≫
      ((M'.X ◁ chainDelta2 A M M' d 0 1) ≫
        chainInsP A M M' (0 + 1) (1 + 1)) :=
    whisker_eq _ (whisker_eq _ (whisker_eq _
      (whisker_eq _ hU4)))
  have C5 : (M'.X ◁ chainInsQ A M M' 0 0) ≫
      ((M'.X ◁ chainDelta2 A M M' d 0 1) ≫
        chainInsP A M M' (0 + 1) (1 + 1)) =
    (M'.X ◁ (M.X ◁ chainDelta2 A M M' d 0 0)) ≫
      (M'.X ◁ chainInsQ A M M' (0 + 1) (0 + 1)) ≫
      chainInsP A M M' (0 + 1) (1 + 1) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker
        ((MonoidalCategory.whiskerLeft_comp _ _ _).symm.trans
          ((congrArg (fun t => M'.X ◁ t) hU5).trans
            (MonoidalCategory.whiskerLeft_comp _ _ _))) _).trans
        (Category.assoc _ _ _))
  have C6 : ((M'.X ⊗ M.X) ◁ chainSeed A M M' d) ≫
      (α_ M'.X M.X (chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ (M.X ◁ chainDelta2 A M M' d 0 0)) ≫
      (M'.X ◁ chainInsQ A M M' (0 + 1) (0 + 1)) ≫
      chainInsP A M M' (0 + 1) (1 + 1) =
    (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
        chainDelta2 A M M' d 0 0))) ≫
      (M'.X ◁ chainInsQ A M M' (0 + 1) (0 + 1)) ≫
      chainInsP A M M' (0 + 1) (1 + 1) :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker hU6 _).trans
        ((Category.assoc _ _ _).trans (whisker_eq _
          ((Category.assoc _ _ _).symm.trans
            (eq_whisker
              ((MonoidalCategory.whiskerLeft_comp
                _ _ _).symm.trans
                (congrArg (fun t => M'.X ◁ t)
                  (MonoidalCategory.whiskerLeft_comp
                    _ _ _).symm)) _)))))
  exact C12.trans (C3.trans (C4.trans
    ((whisker_eq _ (whisker_eq _ (whisker_eq _ C5))).trans
      (whisker_eq _ C6))))

/-- The unit-strand coherence of the two seed routes. -/
private theorem pairPrefix_coh
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (M : Mod D A) (M' : Mod D A) :
    ((ρ_ M'.X).inv ▷ M.X) ≫ (α_ M'.X (𝟙_ D) M.X).hom ≫
      (M'.X ◁ ((β_ (𝟙_ D) M.X).hom ≫
        ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
        (α_ M.X (𝟙_ D) (𝟙_ D)).hom)) =
    (ρ_ (M'.X ⊗ M.X)).inv ≫ (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (ρ_ (𝟙_ D)).inv)) := by
  rw [braiding_tensorUnit_left]
  monoidal

/-- A point whiskered onto the left braids to the unit strand. -/
private theorem seedShuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (M : Mod D A) {S : D} (t : 𝟙_ D ⟶ S) :
    (t ▷ M.X) ≫ (β_ S M.X).hom ≫ ((ρ_ M.X).inv ▷ S) ≫
      (α_ M.X (𝟙_ D) S).hom =
    (β_ (𝟙_ D) M.X).hom ≫ ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
      (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫
      (M.X ◁ ((𝟙_ D) ◁ t)) := by
  have h1 : (t ▷ M.X) ≫ (β_ S M.X).hom =
      (β_ (𝟙_ D) M.X).hom ≫ (M.X ◁ t) :=
    BraidedCategory.braiding_naturality_left _ _
  have h2 : (M.X ◁ t) ≫ ((ρ_ M.X).inv ▷ S) =
      ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫ ((M.X ⊗ (𝟙_ D)) ◁ t) :=
    whisker_exchange _ _
  have h3 : ((M.X ⊗ (𝟙_ D)) ◁ t) ≫
      (α_ M.X (𝟙_ D) S).hom =
    (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫ (M.X ◁ ((𝟙_ D) ◁ t)) :=
    associator_naturality_right _ _ _
  calc (t ▷ M.X) ≫ (β_ S M.X).hom ≫
      ((ρ_ M.X).inv ▷ S) ≫ (α_ M.X (𝟙_ D) S).hom
      = (β_ (𝟙_ D) M.X).hom ≫ ((M.X ◁ t) ≫
          ((ρ_ M.X).inv ▷ S)) ≫ (α_ M.X (𝟙_ D) S).hom := by
        rw [← Category.assoc, h1]
        simp only [Category.assoc]
    _ = (β_ (𝟙_ D) M.X).hom ≫ ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
          (((M.X ⊗ (𝟙_ D)) ◁ t) ≫
            (α_ M.X (𝟙_ D) S).hom) := by
        rw [h2]
        simp only [Category.assoc]
    _ = (β_ (𝟙_ D) M.X).hom ≫ ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
          (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫
          (M.X ◁ ((𝟙_ D) ◁ t)) := by
        rw [h3]

/-- The unit-strand coherence, with a generic continuation. -/
private theorem pairPrefix_coh'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (M : Mod D A) (M' : Mod D A) {T : D}
    (g : M.X ⊗ ((𝟙_ D) ⊗ (𝟙_ D)) ⟶ T) :
    ((ρ_ M'.X).inv ▷ M.X) ≫ (α_ M'.X (𝟙_ D) M.X).hom ≫
      (M'.X ◁ ((β_ (𝟙_ D) M.X).hom ≫
        ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
        (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫ g)) =
    (ρ_ (M'.X ⊗ M.X)).inv ≫ (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ ((M.X ◁ (ρ_ (𝟙_ D)).inv) ≫ g)) := by
  have hsplit : M'.X ◁ ((β_ (𝟙_ D) M.X).hom ≫
      ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
      (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫ g) =
    (M'.X ◁ ((β_ (𝟙_ D) M.X).hom ≫
      ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
      (α_ M.X (𝟙_ D) (𝟙_ D)).hom)) ≫ (M'.X ◁ g) := by
    simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
  have hsplit' : M'.X ◁ ((M.X ◁ (ρ_ (𝟙_ D)).inv) ≫ g) =
      (M'.X ◁ (M.X ◁ (ρ_ (𝟙_ D)).inv)) ≫ (M'.X ◁ g) :=
    MonoidalCategory.whiskerLeft_comp _ _ _
  rw [hsplit, hsplit']
  rw [reassoc_of% (pairPrefix_coh A M M')]

private theorem pairSeed_tensor_prefix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0)))
      = (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷ M.X) ≫
          (α_ M'.X (chainStage2 A M M' 0 0) M.X).hom ≫
          (M'.X ◁ (((chainStage2 A M M' 0 0) ◁
            ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
            (β_ (chainStage2 A M M' 0 0)
              (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
            (α_ M.X (chainStage2 A M M' 0 0)
              (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ chainMul2 A M M' 0 0 0 0)))  := by
  have hD1 : (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) =
    (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷ M.X) ≫
      ((M'.X ⊗ (chainStage2 A M M' 0 0)) ◁
        ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) :=
    MonoidalCategory.tensorHom_def _ _
  have hD2 : ((M'.X ⊗ (chainStage2 A M M' 0 0)) ◁
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom =
    (α_ M'.X (chainStage2 A M M' 0 0) M.X).hom ≫
      (M'.X ◁ ((chainStage2 A M M' 0 0) ◁
        ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)))) :=
    associator_naturality_right _ _ _
  rw [hD1]
  simp only [Category.assoc]
  rw [← Category.assoc ((M'.X ⊗ (chainStage2 A M M' 0 0)) ◁
    ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
  (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))), hD2]
  simp only [Category.assoc,
    MonoidalCategory.whiskerLeft_comp]

/-- **The two seed routes agree**: feeding the seeds through the
pair equals feeding them through the transition. -/
private theorem pairSeed_match
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0))) =
    (ρ_ (M'.X ⊗ M.X)).inv ≫ (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
        chainDelta2 A M M' d 0 0))) := by
  have hD4 : ((chainStage2 A M M' 0 0) ◁
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
      (β_ (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom =
    (β_ (chainStage2 A M M' 0 0) M.X).hom ≫
      (((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷
        (chainStage2 A M M' 0 0)) :=
    BraidedCategory.braiding_naturality_right _ _
  have hD6 : ((MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷
        (chainStage2 A M M' 0 0)) ≫
      (α_ M.X (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 0)).hom =
    (α_ M.X (𝟙_ D) (chainStage2 A M M' 0 0)).hom ≫
      (M.X ◁ (chainSeed A M M' d ▷ (chainStage2 A M M' 0 0))) :=
    associator_naturality_middle _ _ _
  have hD8 : ((MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷ M.X) ≫
      (α_ M'.X (chainStage2 A M M' 0 0) M.X).hom =
    (α_ M'.X (𝟙_ D) M.X).hom ≫
      (M'.X ◁ (chainSeed A M M' d ▷ M.X)) :=
    associator_naturality_middle _ _ _
  have hD10 : (chainSeed A M M' d ▷ M.X) ≫
      (β_ (chainStage2 A M M' 0 0) M.X).hom =
    (β_ (𝟙_ D) M.X).hom ≫ (M.X ◁ chainSeed A M M' d) :=
    BraidedCategory.braiding_naturality_left _ _
  have hD11 : (M.X ◁ chainSeed A M M' d) ≫
      ((ρ_ M.X).inv ▷ (chainStage2 A M M' 0 0)) =
    ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
      ((M.X ⊗ (𝟙_ D)) ◁ chainSeed A M M' d) :=
    whisker_exchange _ _
  have hD12 : ((M.X ⊗ (𝟙_ D)) ◁ chainSeed A M M' d) ≫
      (α_ M.X (𝟙_ D) (chainStage2 A M M' 0 0)).hom =
    (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫
      (M.X ◁ ((𝟙_ D) ◁ chainSeed A M M' d)) :=
    associator_naturality_right _ _ _
  have hSeed : chainSeed A M M' d ≫
      chainDelta2 A M M' d 0 0 =
    (ρ_ (𝟙_ D)).inv ≫ ((𝟙_ D) ◁ chainSeed A M M' d) ≫
      ((chainSeed A M M' d ▷ (chainStage2 A M M' 0 0)) ≫
        chainMul2 A M M' 0 0 0 0) :=
    comp_chainDelta2 A M M' d 0 0 (chainSeed A M M' d)
  -- Assemble: reduce the left side to the coherence prefix
  -- against the common seed tail, then close by the unit-strand
  -- coherence.
  calc (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0)))
      = (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷ M.X) ≫
          (α_ M'.X (chainStage2 A M M' 0 0) M.X).hom ≫
          (M'.X ◁ (((chainStage2 A M M' 0 0) ◁
            ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d))) ≫
            (β_ (chainStage2 A M M' 0 0)
              (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
            (α_ M.X (chainStage2 A M M' 0 0)
              (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ chainMul2 A M M' 0 0 0 0))) := pairSeed_tensor_prefix A M M' d
    _ = (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷ M.X) ≫
          (α_ M'.X (chainStage2 A M M' 0 0) M.X).hom ≫
          (M'.X ◁ ((β_ (chainStage2 A M M' 0 0) M.X).hom ≫
            ((ρ_ M.X).inv ▷ (chainStage2 A M M' 0 0)) ≫
            ((MonoidalCategory.whiskerLeft M.X
              (Y₂ := chainStage2 A M M' 0 0)
              (chainSeed A M M' d)) ▷
              (chainStage2 A M M' 0 0)) ≫
            (α_ M.X (chainStage2 A M M' 0 0)
              (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ chainMul2 A M M' 0 0 0 0))) := by
        refine whisker_eq _ (whisker_eq _
          (congrArg (fun t => M'.X ◁ t) ?_))
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (eq_whisker hD4 _).trans ?_
        simp only [Category.assoc,
          MonoidalCategory.comp_whiskerRight]
    _ = (((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ▷ M.X) ≫
          (α_ M'.X (chainStage2 A M M' 0 0) M.X).hom ≫
          (M'.X ◁ ((β_ (chainStage2 A M M' 0 0) M.X).hom ≫
            ((ρ_ M.X).inv ▷ (chainStage2 A M M' 0 0)) ≫
            (α_ M.X (𝟙_ D) (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ ((chainSeed A M M' d ▷
              (chainStage2 A M M' 0 0)) ≫
              chainMul2 A M M' 0 0 0 0)))) := by
        refine whisker_eq _ (whisker_eq _
          (congrArg (fun t => M'.X ◁ t)
            (whisker_eq _ (whisker_eq _ ?_))))
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (eq_whisker hD6 _).trans ?_
        refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
        exact (MonoidalCategory.whiskerLeft_comp _ _ _).symm
    _ = ((ρ_ M'.X).inv ▷ M.X) ≫
          (α_ M'.X (𝟙_ D) M.X).hom ≫
          (M'.X ◁ (((chainSeed A M M' d) ▷ M.X) ≫
            (β_ (chainStage2 A M M' 0 0) M.X).hom ≫
            ((ρ_ M.X).inv ▷ (chainStage2 A M M' 0 0)) ≫
            (α_ M.X (𝟙_ D) (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ ((chainSeed A M M' d ▷
              (chainStage2 A M M' 0 0)) ≫
              chainMul2 A M M' 0 0 0 0)))) := by
        refine (eq_whisker
          (MonoidalCategory.comp_whiskerRight
            (ρ_ M'.X).inv (MonoidalCategory.whiskerLeft M'.X
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) M.X) _).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine whisker_eq _ ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (eq_whisker hD8 _).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine whisker_eq _ ?_
        exact (MonoidalCategory.whiskerLeft_comp _ _ _).symm
    _ = ((ρ_ M'.X).inv ▷ M.X) ≫
          (α_ M'.X (𝟙_ D) M.X).hom ≫
          (M'.X ◁ ((β_ (𝟙_ D) M.X).hom ≫
            ((ρ_ M.X).inv ▷ (𝟙_ D)) ≫
            (α_ M.X (𝟙_ D) (𝟙_ D)).hom ≫
            (M.X ◁ (((𝟙_ D) ◁ chainSeed A M M' d) ≫
              ((chainSeed A M M' d ▷
                (chainStage2 A M M' 0 0)) ≫
                chainMul2 A M M' 0 0 0 0))))) := by
        refine whisker_eq _ (whisker_eq _
          (congrArg (fun t => M'.X ◁ t) ?_))
        have hre : ((chainSeed A M M' d) ▷ M.X) ≫
            (β_ (chainStage2 A M M' 0 0) M.X).hom ≫
            ((ρ_ M.X).inv ▷ (chainStage2 A M M' 0 0)) ≫
            (α_ M.X (𝟙_ D) (chainStage2 A M M' 0 0)).hom ≫
            (M.X ◁ ((chainSeed A M M' d ▷
              (chainStage2 A M M' 0 0)) ≫
              chainMul2 A M M' 0 0 0 0)) =
          (((chainSeed A M M' d) ▷ M.X) ≫
            (β_ (chainStage2 A M M' 0 0) M.X).hom ≫
            ((ρ_ M.X).inv ▷ (chainStage2 A M M' 0 0)) ≫
            (α_ M.X (𝟙_ D) (chainStage2 A M M' 0 0)).hom) ≫
            (M.X ◁ ((chainSeed A M M' d ▷
              (chainStage2 A M M' 0 0)) ≫
              chainMul2 A M M' 0 0 0 0)) := by
          repeat' erw [Category.assoc]
        refine hre.trans ?_
        refine (eq_whisker (seedShuffle A M
          (S := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) _).trans ?_
        simp only [Category.assoc]
        refine whisker_eq _ (whisker_eq _ (whisker_eq _ ?_))
        exact (MonoidalCategory.whiskerLeft_comp _ _ _).symm
    _ = (ρ_ (M'.X ⊗ M.X)).inv ≫
          (α_ M'.X M.X (𝟙_ D)).hom ≫
          (M'.X ◁ ((M.X ◁ (ρ_ (𝟙_ D)).inv) ≫
            (M.X ◁ (((𝟙_ D) ◁ chainSeed A M M' d) ≫
              ((chainSeed A M M' d ▷
                (chainStage2 A M M' 0 0)) ≫
                chainMul2 A M M' 0 0 0 0))))) :=
        pairPrefix_coh' A M M' _
    _ = (ρ_ (M'.X ⊗ M.X)).inv ≫
          (α_ M'.X M.X (𝟙_ D)).hom ≫
          (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
            chainDelta2 A M M' d 0 0))) := by
        refine whisker_eq _ (whisker_eq _
          (congrArg (fun t => M'.X ◁ t) ?_))
        refine ((MonoidalCategory.whiskerLeft_comp
          _ _ _).symm.trans
          (congrArg (fun t => M.X ◁ t) ?_))
        exact hSeed.symm

/-- The seed-route agreement, with a generic continuation. -/
private theorem pairSeed_match'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') {T : D} (g : M'.X ⊗ (M.X ⊗ chainStage2 A M M'
      (0 + 1) (0 + 1)) ⟶ T) :
    ((((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
      (Y₂ := chainStage2 A M M' 0 0)
      (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0)
        (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0))) ≫ g) =
    (ρ_ (M'.X ⊗ M.X)).inv ≫ (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
        chainDelta2 A M M' d 0 0))) ≫ g := by
  have h1 : ((((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
      (Y₂ := chainStage2 A M M' 0 0)
      (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0)
        (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0))) ≫ g) =
    ((((ρ_ M'.X).inv ≫ MonoidalCategory.whiskerLeft M'.X
      (Y₂ := chainStage2 A M M' 0 0)
      (chainSeed A M M' d)) ⊗ₘ
      ((ρ_ M.X).inv ≫ MonoidalCategory.whiskerLeft M.X
        (Y₂ := chainStage2 A M M' 0 0)
        (chainSeed A M M' d))) ≫
      (α_ M'.X (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
          (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
        (α_ M.X (chainStage2 A M M' 0 0)
          (chainStage2 A M M' 0 0)).hom ≫
        (M.X ◁ chainMul2 A M M' 0 0 0 0)))) ≫ g := by
    simp only [Category.assoc]
  have h2 : (ρ_ (M'.X ⊗ M.X)).inv ≫
      (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
        chainDelta2 A M M' d 0 0))) ≫ g =
    ((ρ_ (M'.X ⊗ M.X)).inv ≫
      (α_ M'.X M.X (𝟙_ D)).hom ≫
      (M'.X ◁ (M.X ◁ (chainSeed A M M' d ≫
        chainDelta2 A M M' d 0 0)))) ≫ g := by
    simp only [Category.assoc]
  rw [h1, h2, pairSeed_match]

/-- **The raw pair product is the swapped base element against
the double transition.** -/
theorem chainPairRaw_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    chainPairRaw A M M' d =
      (β_ M.X M'.X).hom ≫
        (((((symPowOne A M'.X).inv ⊗ₘ
          (symPowOne A M.X).inv) ≫
          modTensorπ A (symPowMod A M'.X 0) (symPowMod A M.X 0)) ≫
          chainDelta2 A M M' d 0 0) ≫
          chainDelta2 A M M' d 1 1) := by
  rw [pairRaw_normal, swapDelta_normal]
  refine whisker_eq _ ?_
  have hsplit : M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
      (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (α_ M.X (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 0)).hom ≫
      (M.X ◁ chainMul2 A M M' 0 0 0 0) ≫
      chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0)) =
    (M'.X ◁ ((β_ (chainStage2 A M M' 0 0)
        (M.X ⊗ chainStage2 A M M' 0 0)).hom ≫
      (α_ M.X (chainStage2 A M M' 0 0)
        (chainStage2 A M M' 0 0)).hom ≫
      (M.X ◁ chainMul2 A M M' 0 0 0 0))) ≫
      (M'.X ◁ chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0)) := by
    simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
  rw [hsplit]
  rw [show chainInsQ A M M' (0 + 1 + 0) (0 + 1 + 0) =
    chainInsQ A M M' (0 + 1) (0 + 1) from rfl]
  rw [show chainInsP A M M' (0 + 1 + 0) (0 + 1 + 1) =
    chainInsP A M M' (0 + 1) (1 + 1) from rfl]
  refine Eq.trans
    (whisker_eq _ (whisker_eq _ (Category.assoc _ _ _))) ?_
  exact pairSeed_match' A M M' d
    ((M'.X ◁ chainInsQ A M M' (0 + 1) (0 + 1)) ≫
      chainInsP A M M' (0 + 1) (1 + 1))

/-- **The descended pair product is the swap, the pair
embedding, and the double transition** — the map form of the
section identity. -/
theorem chainPairMul_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    chainPairMul A M M' d =
      modTensorSwap A M M' ≫
        modTensorMap A (toSymPowModZero A M') (toSymPowModZero A M) ≫
        chainDelta2 A M M' d 0 0 ≫
        chainDelta2 A M M' d 1 1 := by
  refine modTensor_hom_ext A M M' ?_
  rw [modTensorπ_chainPairMul, chainPairRaw_eq]
  have hRside : modTensorπ A M M' ≫ modTensorSwap A M M' ≫
      modTensorMap A (toSymPowModZero A M')
        (toSymPowModZero A M) ≫
      chainDelta2 A M M' d 0 0 ≫
      chainDelta2 A M M' d 1 1 =
    (β_ M.X M'.X).hom ≫
      (((symPowOne A M'.X).inv ⊗ₘ (symPowOne A M.X).inv) ≫
        modTensorπ A (symPowMod A M'.X 0)
          (symPowMod A M.X 0)) ≫
      chainDelta2 A M M' d 0 0 ≫
      chainDelta2 A M M' d 1 1 := by
    rw [modTensorπ_swap_assoc, modTensorπ_map_assoc]
    rw [show (toSymPowModZero A M').hom =
      (symPowOne A M'.X).inv from rfl,
      show (toSymPowModZero A M).hom =
        (symPowOne A M.X).inv from rfl]
    repeat' erw [Category.assoc]
    rfl
  rw [hRside]
  exact whisker_eq _ (Category.assoc _ _ _)

/-- **The copair element multiplies to the doubly advanced
seed**: the element form of the section identity. -/
theorem copairUnit_chainPairMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    copairUnit A M M' d ≫ chainPairMul A M M' d =
      chainSeed A M M' d ≫ chainDelta2 A M M' d 0 0 ≫
        chainDelta2 A M M' d 1 1 := by
  rw [chainPairMul_eq]
  have h : copairUnit A M M' d ≫ modTensorSwap A M M' ≫
      modTensorMap A (toSymPowModZero A M')
        (toSymPowModZero A M) = chainSeed A M M' d := rfl
  exact (whisker_eq _ (Category.assoc _ _ _).symm).trans
    ((Category.assoc _ _ _).symm.trans (eq_whisker h _))

end PairMul

end RS
