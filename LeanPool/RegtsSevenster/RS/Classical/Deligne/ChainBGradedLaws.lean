/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBGraded

/-!
# Laws of the graded line multiplication

Commutativity and associativity of the multiplication of shifted
graded components: the braiding followed by the swapped
multiplication is the multiplication, and the two bracketings of a
triple product agree, in both cases up to the offset transports.
Each law descends from the corresponding two-index stage law of
`ChainStage2` through pair and triple extensionality for tensored
chain colimits, mirroring the homogeneous laws of `ChainAlgebra`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Extensionality for tensors of distinct chain colimits -/

section HetExt

variable {E : Type u}

/-- Absorb a whiskered morphism into the first tensor factor. -/
private theorem tensorHom_whiskerRight_comp
    [Category.{v} E] [MonoidalCategory E]
    {X₁ X₂ Y₁ Y₂ Z₁ W : E} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (f : Y₁ ⟶ Z₁) (r : Z₁ ⊗ Y₂ ⟶ W) :
    (a ⊗ₘ b) ≫ (f ▷ Y₂) ≫ r = ((a ≫ f) ⊗ₘ b) ≫ r := by
  rw [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id]

/-- Absorb a whiskered morphism into the second tensor factor. -/
private theorem tensorHom_whiskerLeft_comp [Category.{v} E] [MonoidalCategory E]
    {X₁ X₂ Y₁ Y₂ Z₂ W : E} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (g : Y₂ ⟶ Z₂) (r : Y₁ ⊗ Z₂ ⟶ W) :
    (a ⊗ₘ b) ≫ (Y₁ ◁ g) ≫ r = (a ⊗ₘ (b ≫ g)) ≫ r := by
  rw [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id]

/-- Extract a prefix of the first tensor factor as a whisker. -/
private theorem compTensorHom_whiskerRight_split
    [Category.{v} E] [MonoidalCategory E]
    {V₁ W₁ U₁ X₂ U₂ Z : E} (x : V₁ ⟶ W₁) (q₁ : W₁ ⟶ U₁)
    (q₂ : X₂ ⟶ U₂) (r : U₁ ⊗ U₂ ⟶ Z) :
    ((x ≫ q₁) ⊗ₘ q₂) ≫ r = (x ▷ X₂) ≫ (q₁ ⊗ₘ q₂) ≫ r := by
  rw [MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_def, comp_whiskerRight]
  simp only [Category.assoc]

/-- Extract a prefix of the second tensor factor as a whisker. -/
private theorem compTensorHom_whiskerLeft_split
    [Category.{v} E] [MonoidalCategory E]
    {X₁ U₁ V₂ W₂ U₂ Z : E} (q₁ : X₁ ⟶ U₁) (x : V₂ ⟶ W₂)
    (q₂ : W₂ ⟶ U₂) (r : U₁ ⊗ U₂ ⟶ Z) :
    (q₁ ⊗ₘ (x ≫ q₂)) ≫ r = (X₁ ◁ x) ≫ (q₁ ⊗ₘ q₂) ≫ r := by
  rw [MonoidalCategory.tensorHom_def',
    MonoidalCategory.tensorHom_def',
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]

/-- Maps out of a tensor of two chain colimits agree once they
agree on all pairs of stages. -/
theorem chainColimitHet_pair_hom_ext [Category.{v} E] [MonoidalCategory E]
    [HasColimitsOfShape SmallNat.{v} E] (B : ℕ → E) (C : ℕ → E)
    (δB : ∀ n, B n ⟶ B (n + 1)) (δC : ∀ n, C n ⟶ C (n + 1))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    {Z : E}
    {f g : chainColimit B δB ⊗ chainColimit C δC ⟶ Z}
    (w : ∀ i j : ℕ,
      (chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ≫ f =
        (chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ≫ g) :
    f = g := by
  apply tensorLeft_chainColimit_hom_ext C δC
  intro j
  apply chainColimit_tensorRight_hom_ext B δB
  intro i
  rw [← Category.assoc, ← Category.assoc,
    show chainColimitι B δB i ▷ C j ≫
        chainColimit B δB ◁ chainColimitι C δC j =
      chainColimitι B δB i ⊗ₘ chainColimitι C δC j from
        (tensorHom_def _ _).symm]
  exact w i j

/-- Maps out of a tensor of two chain colimits whiskered on the
right agree once they agree on all pairs of stages. -/
theorem chainColimitHet_pair_whiskerRight_hom_ext
    [Category.{v} E] [MonoidalCategory E]
    [HasColimitsOfShape SmallNat.{v} E] (B : ℕ → E) (C : ℕ → E)
    (δB : ∀ n, B n ⟶ B (n + 1)) (δC : ∀ n, C n ⟶ C (n + 1))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    {X Z : E}
    {f g : (chainColimit B δB ⊗ chainColimit C δC) ⊗ X ⟶ Z}
    (w : ∀ i j : ℕ,
      ((chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ▷ X) ≫ f =
        ((chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ▷ X) ≫
          g) :
    f = g := by
  apply (cancel_epi (α_ (chainColimit B δB) (chainColimit C δC)
    X).inv).mp
  apply chainColimit_tensorRight_hom_ext B δB
  intro i
  apply chainColimit_sandwich_hom_ext C δC (B i) X
  intro j
  have hpre : (B i ◁ chainColimitι C δC j ▷ X) ≫
      (chainColimitι B δB i ▷ (chainColimit C δC ⊗ X)) ≫
        (α_ (chainColimit B δB) (chainColimit C δC) X).inv =
    (α_ (B i) (C j) X).inv ≫
      ((chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ▷ X) := by
    rw [whisker_exchange_assoc,
      associator_inv_naturality_middle,
      associator_inv_naturality_left_assoc,
      ← comp_whiskerRight, ← tensorHom_def]
  rw [reassoc_of% hpre, reassoc_of% hpre]
  exact congrArg (CategoryStruct.comp _) (w i j)

/-- Maps out of a triple tensor of chain colimits agree once they
agree on all triples of stages. -/
theorem chainColimitHet_triple_hom_ext [Category.{v} E] [MonoidalCategory E]
    [HasColimitsOfShape SmallNat.{v} E] (B : ℕ → E) (C : ℕ → E) (F : ℕ → E)
    (δB : ∀ n, B n ⟶ B (n + 1)) (δC : ∀ n, C n ⟶ C (n + 1))
    (δF : ∀ n, F n ⟶ F (n + 1))
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    {Z : E}
    {f g : (chainColimit B δB ⊗ chainColimit C δC) ⊗
      chainColimit F δF ⟶ Z}
    (w : ∀ i j k : ℕ,
      ((chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ⊗ₘ
          chainColimitι F δF k) ≫ f =
        ((chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ⊗ₘ
          chainColimitι F δF k) ≫ g) :
    f = g := by
  apply tensorLeft_chainColimit_hom_ext F δF
  intro k
  apply chainColimitHet_pair_whiskerRight_hom_ext B C δB δC
  intro i j
  rw [← Category.assoc, ← Category.assoc,
    show (chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ▷ F k ≫
        (chainColimit B δB ⊗ chainColimit C δC) ◁
          chainColimitι F δF k =
      (chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ⊗ₘ
        chainColimitι F δF k from (tensorHom_def _ _).symm]
  exact w i j k

end HetExt

/-! ## The stage-level laws -/

variable {D : Type u}

/-- Stage transports slide out of the first factor of the two-index
multiplication. -/
theorem chainStage2Cast_whiskerRight_chainMul2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {p q p' q' : ℕ} (hp : p = p') (hq : q = q') (e f : ℕ) :
    (chainStage2Cast A M M' hp hq ▷ chainStage2 A M M' e f) ≫
        chainMul2 A M M' p' q' e f =
      chainMul2 A M M' p q e f ≫
        chainStage2Cast A M M' (by omega : p + 1 + e = p' + 1 + e)
          (by omega : q + 1 + f = q' + 1 + f) := by
  subst hp hq
  rw [chainStage2Cast_rfl, chainStage2Cast_rfl,
    MonoidalCategory.id_whiskerRight, Category.id_comp,
    Category.comp_id]

/-- Stage transports slide out of the second factor of the
two-index multiplication. -/
theorem whiskerLeft_chainStage2Cast_chainMul2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (a b : ℕ) {p q p' q' : ℕ} (hp : p = p') (hq : q = q') :
    (chainStage2 A M M' a b ◁ chainStage2Cast A M M' hp hq) ≫
        chainMul2 A M M' a b p' q' =
      chainMul2 A M M' a b p q ≫
        chainStage2Cast A M M' (by omega : a + 1 + p = a + 1 + p')
          (by omega : b + 1 + q = b + 1 + q') := by
  subst hp hq
  rw [chainStage2Cast_rfl, chainStage2Cast_rfl,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Category.comp_id]

/-- **Commutativity of the stagewise line multiplication**, up to
the stage transport onto the common arities. -/
theorem chainBdegMulStage_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p₀ q₀ r₀ s₀ i j : ℕ) :
    (β_ (chainStage2 A M M' (p₀ + i) (q₀ + i))
        (chainStage2 A M M' (r₀ + j) (s₀ + j))).hom ≫
        chainBdegMulStage A M M' r₀ s₀ p₀ q₀ j i ≫
        chainStage2Cast A M M'
          (by omega : r₀ + p₀ + (j + 1 + i) =
            p₀ + r₀ + (i + 1 + j))
          (by omega : s₀ + q₀ + (j + 1 + i) =
            q₀ + s₀ + (i + 1 + j)) =
      chainBdegMulStage A M M' p₀ q₀ r₀ s₀ i j := by
  rw [chainBdegMulStage, chainBdegMulStage,
    ← chainMul2_comm A M M' (p₀ + i) (q₀ + i) (r₀ + j) (s₀ + j)]
  simp only [Category.assoc, chainStage2Cast_trans]

/-- **Associativity of the stagewise line multiplication**, up to
the stage transport reassociating the offsets. -/
theorem chainBdegMulStage_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p₀ q₀ r₀ s₀ t₀ u₀ i j k : ℕ) :
    (chainBdegMulStage A M M' p₀ q₀ r₀ s₀ i j ▷
        chainStage2 A M M' (t₀ + k) (u₀ + k)) ≫
        chainBdegMulStage A M M' (p₀ + r₀) (q₀ + s₀) t₀ u₀
          (i + 1 + j) k =
      (α_ (chainStage2 A M M' (p₀ + i) (q₀ + i))
          (chainStage2 A M M' (r₀ + j) (s₀ + j))
          (chainStage2 A M M' (t₀ + k) (u₀ + k))).hom ≫
        (chainStage2 A M M' (p₀ + i) (q₀ + i) ◁
          chainBdegMulStage A M M' r₀ s₀ t₀ u₀ j k) ≫
        chainBdegMulStage A M M' p₀ q₀ (r₀ + t₀) (s₀ + u₀) i
          (j + 1 + k) ≫
        chainStage2Cast A M M'
          (by omega : p₀ + (r₀ + t₀) + (i + 1 + (j + 1 + k)) =
            p₀ + r₀ + t₀ + (i + 1 + j + 1 + k))
          (by omega : q₀ + (s₀ + u₀) + (i + 1 + (j + 1 + k)) =
            q₀ + s₀ + u₀ + (i + 1 + j + 1 + k)) := by
  have hass := chainMul2_assoc A M M' (p₀ + i) (q₀ + i)
    (r₀ + j) (s₀ + j) (t₀ + k) (u₀ + k)
  rw [show chainStage2Cast A M M'
        (by omega : p₀ + i + 1 + (r₀ + j) + 1 + (t₀ + k) =
          p₀ + i + 1 + (r₀ + j) + 1 + (t₀ + k))
        (by omega : q₀ + i + 1 + (s₀ + j) + 1 + (u₀ + k) =
          q₀ + i + 1 + (s₀ + j) + 1 + (u₀ + k)) = 𝟙 _ from
      chainStage2Cast_rfl A M M' _ _, Category.comp_id] at hass
  rw [chainBdegMulStage, chainBdegMulStage, chainBdegMulStage,
    chainBdegMulStage, comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (chainStage2Cast_whiskerRight_chainMul2 A M M'
      (by omega : p₀ + i + 1 + (r₀ + j) = p₀ + r₀ + (i + 1 + j))
      (by omega : q₀ + i + 1 + (s₀ + j) = q₀ + s₀ + (i + 1 + j))
      (t₀ + k) (u₀ + k)),
    reassoc_of% (whiskerLeft_chainStage2Cast_chainMul2 A M M'
      (p₀ + i) (q₀ + i)
      (by omega : r₀ + j + 1 + (t₀ + k) = r₀ + t₀ + (j + 1 + k))
      (by omega : s₀ + j + 1 + (u₀ + k) = s₀ + u₀ + (j + 1 + k))),
    reassoc_of% hass]
  simp only [chainStage2Cast_trans]

/-! ## Transport of the stage insertions -/

/-- Stage transports along a stage-index equality are absorbed by
the stage insertions of a line. -/
theorem chainStage2Cast_chainBdegι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) {a b : ℕ} (h : a = b) :
    chainStage2Cast A M M' (by omega : p₀ + a = p₀ + b)
        (by omega : q₀ + a = q₀ + b) ≫
      chainBdegι A M M' d p₀ q₀ b =
    chainBdegι A M M' d p₀ q₀ a := by
  rw [← chainCast_line A M M' p₀ q₀ h]
  exact chainCast_chainColimitι
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) h

/-- The stage insertions intertwine the offset transports of a line
with the stage transports. -/
theorem chainBdegι_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {p₀ q₀ p₀' q₀' : ℕ} (hp : p₀ = p₀') (hq : q₀ = q₀') (k : ℕ) :
    chainBdegι A M M' d p₀ q₀ k ≫ chainBdegCast A M M' d hp hq =
      chainStage2Cast A M M' (by omega : p₀ + k = p₀' + k)
          (by omega : q₀ + k = q₀' + k) ≫
        chainBdegι A M M' d p₀' q₀' k := by
  subst hp hq
  rw [chainBdegCast_rfl, chainStage2Cast_rfl, Category.comp_id,
    Category.id_comp]

/-! ## The colimit-level laws -/

section MulColimit

/-- Maps out of a tensor of two graded components agree once they
agree on all pairs of stages. -/
theorem chainBdeg_pair_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ r₀ s₀ : ℕ) {Z : D}
    {f g : chainBdeg A M M' d p₀ q₀ ⊗ chainBdeg A M M' d r₀ s₀ ⟶
      Z}
    (w : ∀ i j : ℕ,
      (chainBdegι A M M' d p₀ q₀ i ⊗ₘ
          chainBdegι A M M' d r₀ s₀ j) ≫ f =
        (chainBdegι A M M' d p₀ q₀ i ⊗ₘ
          chainBdegι A M M' d r₀ s₀ j) ≫ g) :
    f = g :=
  chainColimitHet_pair_hom_ext
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainStage2 A M M' (r₀ + k) (s₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (r₀ + k) (s₀ + k)) w

/-- Maps out of a triple tensor of graded components agree once
they agree on all triples of stages. -/
theorem chainBdeg_triple_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ r₀ s₀ t₀ u₀ : ℕ) {Z : D}
    {f g : (chainBdeg A M M' d p₀ q₀ ⊗
      chainBdeg A M M' d r₀ s₀) ⊗ chainBdeg A M M' d t₀ u₀ ⟶ Z}
    (w : ∀ i j k : ℕ,
      ((chainBdegι A M M' d p₀ q₀ i ⊗ₘ
          chainBdegι A M M' d r₀ s₀ j) ⊗ₘ
          chainBdegι A M M' d t₀ u₀ k) ≫ f =
        ((chainBdegι A M M' d p₀ q₀ i ⊗ₘ
          chainBdegι A M M' d r₀ s₀ j) ⊗ₘ
          chainBdegι A M M' d t₀ u₀ k) ≫ g) :
    f = g :=
  chainColimitHet_triple_hom_ext
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainStage2 A M M' (r₀ + k) (s₀ + k))
    (fun k => chainStage2 A M M' (t₀ + k) (u₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (r₀ + k) (s₀ + k))
    (fun k => chainDelta2 A M M' d (t₀ + k) (u₀ + k)) w

/-- **Commutativity of the graded line multiplication**: the
braiding followed by the swapped multiplication is the
multiplication, up to the offset transport. -/
theorem chainBdegMul_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ r₀ s₀ : ℕ) :
    (β_ (chainBdeg A M M' d p₀ q₀)
        (chainBdeg A M M' d r₀ s₀)).hom ≫
        chainBdegMul A M M' d r₀ s₀ p₀ q₀ ≫
        chainBdegCast A M M' d (Nat.add_comm r₀ p₀)
          (Nat.add_comm s₀ q₀) =
      chainBdegMul A M M' d p₀ q₀ r₀ s₀ := by
  apply chainBdeg_pair_hom_ext A M M' d p₀ q₀ r₀ s₀
  intro i j
  rw [BraidedCategory.braiding_naturality_assoc,
    ι_tensorHom_chainBdegMul_assoc A M M' d r₀ s₀ p₀ q₀ j i,
    ι_tensorHom_chainBdegMul A M M' d p₀ q₀ r₀ s₀ i j,
    chainBdegι_cast A M M' d (Nat.add_comm r₀ p₀)
      (Nat.add_comm s₀ q₀) (j + 1 + i),
    ← chainStage2Cast_chainBdegι A M M' d (p₀ + r₀) (q₀ + s₀)
      (by omega : j + 1 + i = i + 1 + j),
    chainStage2Cast_trans_assoc,
    reassoc_of% (chainBdegMulStage_comm A M M' p₀ q₀ r₀ s₀ i j)]

end MulColimit

end RS
