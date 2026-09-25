/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMulLaws
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainAlgebra
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainDelta

/-!
# The transition squares of the splitting chain

The chain transitions are multiplication by the seed, so they
commute with the chain multiplication: multiplying after an
insertion is inserting after multiplying.  These are the
compatibility squares consumed by the colimit algebra.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- **The right transition square**: inserting the seed in the
second factor and multiplying is multiplying and then inserting
the seed. -/
theorem chainDelta_mul_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (i j : ℕ) :
    (chainStage A M M' i ◁ chainDelta A M M' d j) ≫
        chainMul A M M' i (j + 1) =
      chainMul A M M' i j ≫ chainDelta A M M' d (i + 1 + j) := by
  rw [chainDelta, chainDelta]
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]
  have hass := chainMul_assoc A M M' i j 0
  rw [show chainStageCast A M M'
        (by omega : i + 1 + (j + 1 + 0) = i + 1 + j + 1 + 0) =
      𝟙 _ from chainStageCast_rfl A M M' _,
    Category.comp_id] at hass
  rw [show chainMul A M M' (i + 1 + j) 0 ≫
      𝟙 (chainStage A M M' (i + 1 + (j + 1 + 0))) =
    chainMul A M M' (i + 1 + j) 0 from Category.comp_id _]
    at hass
  have hkey : (chainStage A M M' i ◁ chainMul A M M' j 0) ≫
      chainMul A M M' i (j + 1) =
    (α_ (chainStage A M M' i) (chainStage A M M' j)
        (chainStage A M M' 0)).inv ≫
      (chainMul A M M' i j ▷ chainStage A M M' 0) ≫
      chainMul A M M' (i + 1 + j) 0 := by
    have h := congrArg (fun t =>
      (α_ (chainStage A M M' i) (chainStage A M M' j)
        (chainStage A M M' 0)).inv ≫ t) hass
    simp only [Iso.inv_hom_id_assoc] at h
    exact h.symm
  rw [hkey]
  have h1 : (chainStage A M M' i ◁
      (chainStage A M M' j ◁ chainSeed A M M' d)) ≫
      (α_ (chainStage A M M' i) (chainStage A M M' j)
        (chainStage A M M' 0)).inv =
    (α_ (chainStage A M M' i) (chainStage A M M' j)
        (𝟙_ D)).inv ≫
      ((chainStage A M M' i ⊗ chainStage A M M' j) ◁
        chainSeed A M M' d) := by
    rw [← associator_inv_naturality_right]
  rw [reassoc_of% h1]
  have h2 : (chainStage A M M' i ◁
      (ρ_ (chainStage A M M' j)).inv) ≫
      (α_ (chainStage A M M' i) (chainStage A M M' j)
        (𝟙_ D)).inv =
    (ρ_ (chainStage A M M' i ⊗ chainStage A M M' j)).inv := by
    monoidal
  rw [reassoc_of% h2]
  have h3 : ((chainStage A M M' i ⊗ chainStage A M M' j) ◁
      chainSeed A M M' d) ≫
      (chainMul A M M' i j ▷ chainStage A M M' 0) =
    (chainMul A M M' i j ▷ 𝟙_ D) ≫
      (chainStage A M M' (i + 1 + j) ◁ chainSeed A M M' d) :=
    whisker_exchange _ _
  rw [reassoc_of% h3]
  have h4 : (ρ_ (chainStage A M M' i ⊗
      chainStage A M M' j)).inv ≫
      (chainMul A M M' i j ▷ 𝟙_ D) =
    chainMul A M M' i j ≫
      (ρ_ (chainStage A M M' (i + 1 + j))).inv := by
    rw [rightUnitor_inv_naturality]
  rw [reassoc_of% h4]

/-- Transitions transport along index casts. -/
theorem chainStageCast_delta
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {a b : ℕ} (h : a = b) :
    chainStageCast A M M' h ≫ chainDelta A M M' d b =
      chainDelta A M M' d a ≫
        chainStageCast A M M' (by omega : a + 1 = b + 1) := by
  subst h
  rw [chainStageCast_rfl, chainStageCast_rfl,
    Category.id_comp, Category.comp_id]

/-- **The left transition square**: inserting the seed in the
first factor and multiplying is multiplying and then inserting
the seed, up to the index transport. -/
theorem chainDelta_mul_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (i j : ℕ) :
    (chainDelta A M M' d i ▷ chainStage A M M' j) ≫
        chainMul A M M' (i + 1) j =
      chainMul A M M' i j ≫ chainDelta A M M' d (i + 1 + j) ≫
        chainStageCast A M M'
          (Nat.add_right_comm (i + 1) j 1) := by
  have hcm : chainMul A M M' (i + 1) j =
      (β_ (chainStage A M M' (i + 1))
        (chainStage A M M' j)).hom ≫
      chainMul A M M' j (i + 1) ≫
      chainStageCast A M M'
        (by omega : j + 1 + (i + 1) = i + 1 + 1 + j) :=
    (chainMul_comm A M M' (i + 1) j).symm
  rw [hcm]
  have hnat : (chainDelta A M M' d i ▷ chainStage A M M' j) ≫
      (β_ (chainStage A M M' (i + 1))
        (chainStage A M M' j)).hom =
    (β_ (chainStage A M M' i) (chainStage A M M' j)).hom ≫
      (chainStage A M M' j ◁ chainDelta A M M' d i) := by
    rw [BraidedCategory.braiding_naturality_left]
  rw [reassoc_of% hnat]
  rw [reassoc_of% (chainDelta_mul_right A M M' d j i)]
  have hcm2 : (β_ (chainStage A M M' i)
        (chainStage A M M' j)).hom ≫
      chainMul A M M' j i =
    chainMul A M M' i j ≫ chainStageCast A M M'
      (by omega : i + 1 + j = j + 1 + i) := by
    have h := chainMul_comm A M M' i j
    rw [← h, Category.assoc, Category.assoc,
      chainStageCast_trans, chainStageCast_rfl,
      Category.comp_id]
  rw [reassoc_of% hcm2]
  rw [reassoc_of% (chainStageCast_delta A M M' d
    (by omega : i + 1 + j = j + 1 + i))]
  rw [chainStageCast_trans]

/-- **The right unit law of the seed**: multiplying by the seed
on the right is the transition. -/
theorem chainSeed_mul_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (i : ℕ) :
    (chainStage A M M' i ◁ chainSeed A M M' d) ≫
        chainMul A M M' i 0 =
      (ρ_ (chainStage A M M' i)).hom ≫
        chainDelta A M M' d i := by
  rw [chainDelta, Iso.hom_inv_id_assoc]

/-- **The left unit law of the seed**: multiplying by the seed on
the left is the transition, through the unit braiding. -/
theorem chainSeed_mul_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (j : ℕ) :
    (chainSeed A M M' d ▷ chainStage A M M' j) ≫
        chainMul A M M' 0 j =
      (λ_ (chainStage A M M' j)).hom ≫
        chainDelta A M M' d j ≫
        chainStageCast A M M' (by omega : j + 1 = 0 + 1 + j) := by
  have hcm : chainMul A M M' 0 j =
      (β_ (chainStage A M M' 0) (chainStage A M M' j)).hom ≫
      chainMul A M M' j 0 ≫
      chainStageCast A M M' (by omega : j + 1 + 0 = 0 + 1 + j) :=
    (chainMul_comm A M M' 0 j).symm
  rw [hcm]
  have hnat : (chainSeed A M M' d ▷ chainStage A M M' j) ≫
      (β_ (chainStage A M M' 0) (chainStage A M M' j)).hom =
    (β_ (𝟙_ D) (chainStage A M M' j)).hom ≫
      (chainStage A M M' j ◁ chainSeed A M M' d) := by
    rw [BraidedCategory.braiding_naturality_left]
  rw [reassoc_of% hnat]
  rw [reassoc_of% (chainSeed_mul_right A M M' d j)]
  rw [braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- A chain map to a transported index is the chain map followed
by the transport. -/
theorem chainMap_eq_cast [Category.{v} D]
    (B : ℕ → D) (δ : ∀ n, B n ⟶ B (n + 1))
    {m n n' : ℕ} (h : m ≤ n) (hn : n = n') (h' : m ≤ n') :
    chainMap B δ h' = chainMap B δ h ≫ chainCast B hn := by
  subst hn
  rw [chainCast_rfl, Category.comp_id]

/-- The left seed law in chain-map form. -/
theorem chainSeed_mul_left_chainMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (j : ℕ) :
    (chainSeed A M M' d ▷ chainStage A M M' j) ≫
        chainMul A M M' 0 j =
      (λ_ (chainStage A M M' j)).hom ≫
        chainMap (chainStage A M M') (chainDelta A M M' d)
          (Nat.le_add_left j (0 + 1)) := by
  rw [chainSeed_mul_left A M M' d j,
    chainMap_eq_cast (chainStage A M M')
      (chainDelta A M M' d) (Nat.le_succ j)
      (by omega : j + 1 = 0 + 1 + j) (Nat.le_add_left j (0 + 1)),
    chainMap_le_succ]
  rfl

section Colimit

/-- **The algebra of the splitting chain**: the colimit of the
symmetric stages along the seed transitions. -/
noncomputable def chainB
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') : D :=
  chainColimit (chainStage A M M') (chainDelta A M M' d)

/-- **The splitting-chain algebra is a commutative monoid**: the
stage laws transport to the colimit. -/
@[reducible]
noncomputable def chainBMonObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    MonObj (chainB A M M' d) :=
  chainColimitMonObj (chainStage A M M') (chainDelta A M M' d)
    (chainMul A M M') (chainDelta_mul_left A M M' d)
    (chainDelta_mul_right A M M' d) (chainSeed A M M' d)
    (chainSeed_mul_left_chainMap A M M' d)
    (chainSeed_mul_right A M M' d)
    (fun i j k => by
      have h := chainMul_assoc A M M' i j k
      rw [show chainStageCast A M M'
          (by omega : i + 1 + j + 1 + k = i + 1 + j + 1 + k) =
        𝟙 _ from chainStageCast_rfl A M M' _,
        Category.comp_id] at h
      exact h)

/-- **The splitting-chain algebra is commutative**. -/
theorem chainB_isCommMonObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    letI := chainBMonObj A M M' d
    IsCommMonObj (chainB A M M' d) :=
  chainColimit_isCommMonObj (chainStage A M M')
    (chainDelta A M M' d) (chainMul A M M')
    (chainDelta_mul_left A M M' d)
    (chainDelta_mul_right A M M' d) (chainSeed A M M' d)
    (chainSeed_mul_left_chainMap A M M' d)
    (chainSeed_mul_right A M M' d)
    (fun i j k => by
      have h := chainMul_assoc A M M' i j k
      rw [show chainStageCast A M M'
          (by omega : i + 1 + j + 1 + k = i + 1 + j + 1 + k) =
        𝟙 _ from chainStageCast_rfl A M M' _,
        Category.comp_id] at h
      exact h)
    (fun i j => chainMul_comm A M M' i j)

/-- **The unit of the splitting-chain algebra**: the seed at the
bottom stage. -/
noncomputable def chainBUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') :
    𝟙_ D ⟶ chainB A M M' d :=
  chainColimitUnit (chainStage A M M') (chainDelta A M M' d)
    (chainSeed A M M' d)

end Colimit

end RS
