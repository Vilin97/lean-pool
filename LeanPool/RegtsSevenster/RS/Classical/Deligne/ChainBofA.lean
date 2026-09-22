/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainB
import LeanPool.RegtsSevenster.RS.Classical.Deligne.InterchangeAct
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowDatum

/-!
# The structure morphism of the splitting-chain algebra

The base algebra maps to the splitting-chain algebra: act on the
seed at the bottom stage and include.  The unit law is the
generic point-recovery of unital actions; the multiplication law
reduces along the colimit defining equations to the bilinearity
of the stage multiplication over the base.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The base action on a chain stage, typed at the stage.  A
single atom carrying the wrapper type uniformly, so that the
generic action lemmas instantiate without mixed typing. -/
noncomputable def chainStageAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    A ⊗ chainStage A M M' k ⟶ chainStage A M M' k :=
  modTensorAct A (symPowMod A M'.X k) (symPowMod A M.X k)

/-- The stage action is unital. -/
theorem chainStageAct_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    (η[A] ▷ chainStage A M M' k) ≫ chainStageAct A M M' k =
      (λ_ (chainStage A M M' k)).hom :=
  modTensorAct_one A (symPowMod A M'.X k) (symPowMod A M.X k)

/-- The stage action is associative. -/
theorem chainStageAct_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    (μ[A] ▷ chainStage A M M' k) ≫ chainStageAct A M M' k =
      (α_ A A (chainStage A M M' k)).hom ≫
        (A ◁ chainStageAct A M M' k) ≫ chainStageAct A M M' k :=
  modTensorAct_mul A (symPowMod A M'.X k) (symPowMod A M.X k)

/-- **The structure morphism of the splitting-chain algebra**:
act on the seed at the bottom stage and include. -/
noncomputable def chainBofA
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') :
    A ⟶ chainB A M M' d :=
  (ρ_ A).inv ≫ (A ◁ chainSeed A M M' d) ≫
    chainStageAct A M M' 0 ≫
    chainColimitι (chainStage A M M') (chainDelta A M M' d) 0

/-- **The structure morphism preserves the unit**: the unit of
the base recovers the seed, which is the unit of the algebra. -/
theorem chainBofA_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') :
    η[A] ≫ chainBofA A M M' d = chainBUnit A M M' d := by
  have h := act_on_point_unit A (chainStageAct A M M' 0)
    (chainStageAct_one A M M' 0) (chainSeed A M M' d)
  erw [chainBofA, reassoc_of% h]
  rfl

/-- The chain multiplication is left linear over the base, at the
stage typing. -/
theorem chainMul_actLeft_stage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ) :
    (chainStageAct A M M' m ▷ chainStage A M M' n) ≫
        chainMul A M M' m n =
      (α_ A (chainStage A M M' m) (chainStage A M M' n)).hom ≫
        (A ◁ chainMul A M M' m n) ≫
        chainStageAct A M M' (m + 1 + n) :=
  chainMul_actLeft A M M' m n

/-- The stage transport commutes with the action. -/
theorem chainStageCast_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {j k : ℕ} (h : j = k) :
    chainStageAct A M M' j ≫ chainStageCast A M M' h =
      (A ◁ chainStageCast A M M' h) ≫ chainStageAct A M M' k := by
  subst h
  simp [chainStageCast_rfl]

/-- **Insertion maps are linear**: precomposing an action with a
point insertion followed by a linear map is again linear.  The
generic-carrier form; the orbit-map linearity is the case of the
action itself. -/
theorem act_insert_linear [Category.{v} D] [MonoidalCategory D] (A : D)
    {X S Z : D} (actX : A ⊗ X ⟶ X)
    (actZ : A ⊗ Z ⟶ Z) (s : 𝟙_ D ⟶ S) (m : X ⊗ S ⟶ Z)
    (hm : (actX ▷ S) ≫ m =
      (α_ A X S).hom ≫ (A ◁ m) ≫ actZ) :
    actX ≫ (ρ_ X).inv ≫ (X ◁ s) ≫ m =
      (A ◁ ((ρ_ X).inv ≫ (X ◁ s) ≫ m)) ≫ actZ := by
  have hnat : ((A ⊗ X) ◁ s) ≫ (α_ A X S).hom =
      (α_ A X (𝟙_ D)).hom ≫ (A ◁ (X ◁ s)) :=
    associator_naturality_right A X s
  rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc,
    ← Category.assoc (actX ▷ 𝟙_ D), ← whisker_exchange,
    Category.assoc, hm, reassoc_of% hnat,
    ← Category.assoc ((ρ_ (A ⊗ X)).inv),
    (by monoidal : (ρ_ (A ⊗ X)).inv ≫ (α_ A X (𝟙_ D)).hom =
      A ◁ (ρ_ X).inv),
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]

/-- **The chain transition is linear over the base**: it is the
insertion of the seed followed by the multiplication, which is
linear in its first slot. -/
theorem chainDelta_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (k : ℕ) :
    chainStageAct A M M' k ≫ chainDelta A M M' d k =
      (A ◁ chainDelta A M M' d k) ≫
        chainStageAct A M M' (k + 1) := by
  have h := act_insert_linear A (chainStageAct A M M' k)
    (chainStageAct A M M' (k + 1 + 0)) (chainSeed A M M' d)
    (chainMul A M M' k 0) (chainMul_actLeft_stage A M M' k 0)
  exact h

/-- **The chain multiplication is right linear over the base**:
by commutativity, the second-slot action braids to the front and
the left linearity applies. -/
theorem chainMul_actRight_stage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ) :
    (chainStage A M M' m ◁ chainStageAct A M M' n) ≫
        chainMul A M M' m n =
      (α_ (chainStage A M M' m) A (chainStage A M M' n)).inv ≫
        ((β_ (chainStage A M M' m) A).hom ▷ chainStage A M M' n) ≫
        (α_ A (chainStage A M M' m) (chainStage A M M' n)).hom ≫
        (A ◁ chainMul A M M' m n) ≫
        chainStageAct A M M' (m + 1 + n) := by
  have hinv : chainMul A M M' n m ≫
      chainStageCast A M M' (by omega : n + 1 + m = m + 1 + n) =
      (β_ (chainStage A M M' n) (chainStage A M M' m)).hom ≫
        chainMul A M M' m n := by
    conv_rhs => rw [← chainMul_comm A M M' m n,
      SymmetricCategory.braiding_swap_eq_inv_braiding,
      Iso.inv_hom_id_assoc]
  have hcoh : (β_ (chainStage A M M' m)
        (A ⊗ chainStage A M M' n)).hom ≫
      (α_ A (chainStage A M M' n) (chainStage A M M' m)).hom ≫
      (A ◁ (β_ (chainStage A M M' n)
        (chainStage A M M' m)).hom) =
      (α_ (chainStage A M M' m) A (chainStage A M M' n)).inv ≫
        ((β_ (chainStage A M M' m) A).hom ▷
          chainStage A M M' n) ≫
        (α_ A (chainStage A M M' m) (chainStage A M M' n)).hom := by
    rw [BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp]
    rw [SymmetricCategory.symmetry]
    simp
  conv_lhs => rw [← chainMul_comm A M M' m n]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    reassoc_of% (chainMul_actLeft_stage A M M' n m),
    chainStageCast_actLeft,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hinv,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    reassoc_of% hcoh]

/-- Point insertion on the right is natural. -/
theorem insert_point_natural [Category.{v} D] [MonoidalCategory D]
    {X Y S : D} (f : X ⟶ Y)
    (s : 𝟙_ D ⟶ S) :
    f ≫ (ρ_ Y).inv ≫ (Y ◁ s) =
      (ρ_ X).inv ≫ (X ◁ s) ≫ (f ▷ S) := by
  rw [← Category.assoc, rightUnitor_inv_naturality,
    Category.assoc, ← whisker_exchange]

/-- **The stage multiplication law of the structure morphism**:
multiplying two acted seeds is acting by the product on the
doubled seed.  The stage-level core of the algebra-map property. -/
theorem chainBofA_mul_stage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (((ρ_ A).inv ≫ (A ◁ chainSeed A M M' d) ≫
        chainStageAct A M M' 0) ⊗ₘ
      ((ρ_ A).inv ≫ (A ◁ chainSeed A M M' d) ≫
        chainStageAct A M M' 0)) ≫ chainMul A M M' 0 0 =
      μ[A] ≫ (ρ_ A).inv ≫ (A ◁ chainSeed A M M' d) ≫
        chainStageAct A M M' 0 ≫ chainDelta A M M' d 0 := by
  conv_rhs => rw [chainDelta_actLeft A M M' d 0,
    ← MonoidalCategory.whiskerLeft_comp_assoc, chainDelta,
    reassoc_of% (insert_point_natural (chainSeed A M M' d)
      (chainSeed A M M' d))]
  conv_lhs => rw [MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc, chainMul_actRight_stage A M M' 0 0]
  have hdouble : (A ◁ chainStageAct A M M' (0 + 1 + 0)) ≫
      chainStageAct A M M' (0 + 1 + 0) =
      (α_ A A (chainStage A M M' (0 + 1 + 0))).inv ≫
        (μ[A] ▷ chainStage A M M' (0 + 1 + 0)) ≫
        chainStageAct A M M' (0 + 1 + 0) := by
    rw [chainStageAct_mul A M M' (0 + 1 + 0),
      Iso.inv_hom_id_assoc]
  conv_lhs => rw [comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc,
    ← whisker_exchange_assoc (chainStageAct A M M' 0)
      ((ρ_ A).inv),
    ← whisker_exchange_assoc (chainStageAct A M M' 0)
      (A ◁ chainSeed A M M' d),
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc (chainStageAct A M M' 0 ▷ A)
      (β_ (chainStage A M M' 0) A).hom,
    BraidedCategory.braiding_naturality_left,
    comp_whiskerRight, Category.assoc,
    associator_naturality_middle_assoc]
  conv_lhs => rw [
    ← MonoidalCategory.whiskerLeft_comp_assoc A
      (chainStageAct A M M' 0 ▷ chainStage A M M' 0)
      (chainMul A M M' 0 0),
    chainMul_actLeft_stage A M M' 0 0,
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc, hdouble]
  conv_lhs => rw [
    associator_inv_naturality_right_assoc A A
      (chainMul A M M' 0 0),
    whisker_exchange_assoc μ[A] (chainMul A M M' 0 0)]
  -- Slide the second seed insertion to the tail.
  conv_lhs => rw [
    associator_inv_naturality_right_assoc
      (A ⊗ chainStage A M M' 0) A (chainSeed A M M' d),
    whisker_exchange_assoc
      (β_ (A ⊗ chainStage A M M' 0) A).hom (chainSeed A M M' d),
    associator_naturality_right_assoc A
      (A ⊗ chainStage A M M' 0) (chainSeed A M M' d),
    ← MonoidalCategory.whiskerLeft_comp_assoc A
      ((A ⊗ chainStage A M M' 0) ◁ chainSeed A M M' d)
      (α_ A (chainStage A M M' 0) (chainStage A M M' 0)).hom,
    associator_naturality_right A (chainStage A M M' 0)
      (chainSeed A M M' d),
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_right_assoc A A
      (chainStage A M M' 0 ◁ chainSeed A M M' d),
    whisker_exchange_assoc μ[A]
      (chainStage A M M' 0 ◁ chainSeed A M M' d)]
  -- Slide the first seed insertion to the tail.
  conv_lhs => rw [
    ← whisker_exchange_assoc (A ◁ chainSeed A M M' d)
      ((ρ_ A).inv),
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc ((A ◁ chainSeed A M M' d) ▷ A)
      (β_ (A ⊗ chainStage A M M' 0) A).hom,
    BraidedCategory.braiding_naturality_left,
    comp_whiskerRight, Category.assoc,
    associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc A
      ((A ◁ chainSeed A M M' d) ▷ 𝟙_ D)
      (α_ A (chainStage A M M' 0) (𝟙_ D)).hom,
    associator_naturality_middle,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_right_assoc A A
      (chainSeed A M M' d ▷ 𝟙_ D),
    whisker_exchange_assoc μ[A] (chainSeed A M M' d ▷ 𝟙_ D)]
  -- Align the seed insertions with the unfolded transition and
  -- the arities.
  conv_lhs => rw [
    ← MonoidalCategory.whiskerLeft_comp_assoc A
      (chainSeed A M M' d ▷ 𝟙_ D)
      (chainStage A M M' 0 ◁ chainSeed A M M' d),
    ← whisker_exchange (chainSeed A M M' d) (chainSeed A M M' d),
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    (show chainStageAct A M M' (0 + 1 + 0) =
      chainStageAct A M M' (0 + 1) from rfl)]
  -- Expand the right side.
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc, Category.assoc]
  -- The braiding at the unit-padded slot is the conjugated
  -- braiding of the base.
  have hβ : (β_ (A ⊗ 𝟙_ D) A).hom =
      ((ρ_ A).hom ▷ A) ≫ (β_ A A).hom ≫ (A ◁ (ρ_ A).inv) := by
    conv_rhs => rw [← Category.assoc,
      BraidedCategory.braiding_naturality_left, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rw [hβ]
  -- Commutativity supplies the crossing on the right.
  conv_rhs => rw [(show (μ[A] : A ⊗ A ⟶ A) =
    (β_ A A).hom ≫ μ[A] from
      (IsCommMonObj.mul_comm A).symm)]
  monoidal

end RS
