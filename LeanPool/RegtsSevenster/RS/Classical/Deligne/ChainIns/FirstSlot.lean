/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainIns.Base

/-!
# The first-slot insertion against the stage structure

The insertion of a letter into the first slot of a two-index chain
stage, defined in [Base.lean](Base.lean), meets the two structure
maps of the chain: the stage multiplication and the seed
transition.

* `chainInsP_mul`: inserting a letter into a merged stage is
  inserting into the first factor and multiplying, up to the index
  transport.
* `chainInsP_delta2`: the insertion passes the seed transition,
  raising the merged arities by one on each side.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## An insertion past the interchange -/

section InsPastInterchange

/-- An insertion into the first factor of the first pair passes
the interchange. -/
private theorem insL_past_tensorμ [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D]
    {X P P₂ Q R S : D} (f : X ⊗ P ⟶ P₂) :
    (α_ X (P ⊗ Q) (R ⊗ S)).inv ≫
        (((α_ X P Q).inv ≫ (f ▷ Q)) ⊗ₘ 𝟙 (R ⊗ S)) ≫
        tensorμ P₂ Q R S =
      (X ◁ tensorμ P Q R S) ≫
        (α_ X (P ⊗ R) (Q ⊗ S)).inv ≫
        (((α_ X P R).inv ≫ (f ▷ R)) ⊗ₘ 𝟙 (Q ⊗ S)) := by
  have hcoh : (α_ X (P ⊗ Q) (R ⊗ S)).inv ≫
      ((α_ X P Q).inv ▷ (R ⊗ S)) ≫ tensorμ (X ⊗ P) Q R S =
      (X ◁ tensorμ P Q R S) ≫
        (α_ X (P ⊗ R) (Q ⊗ S)).inv ≫
        ((α_ X P R).inv ▷ (Q ⊗ S)) := by
    dsimp only [tensorμ]
    monoidal
  have hnat := tensorμ_natural_left f (𝟙 Q) R S
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_whiskerRight] at hnat
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [hnat, reassoc_of% hcoh]

end InsPastInterchange

/-! ## The insertion against the stage multiplication -/

section InsSurgery

/-- Absorb a whiskered morphism into the first tensor factor. -/
theorem tensorHom_whiskerRight_absorb [Category.{v} D] [MonoidalCategory D]
    {X₁ X₂ Y₁ Y₂ Z₁ W : D} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (f : Y₁ ⟶ Z₁) (h : Z₁ ⊗ Y₂ ⟶ W) :
    (a ⊗ₘ b) ≫ (f ▷ Y₂) ≫ h = ((a ≫ f) ⊗ₘ b) ≫ h := by
  rw [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id]

end InsSurgery

section Ins2Laws

/-- **The insertion passes the stage multiplication**: inserting
a letter into the merged stage is inserting into the first factor
and multiplying, up to the index transport. -/
theorem chainInsP_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q r s : ℕ) :
    (M'.X ◁ chainMul2 A M M' p q r s) ≫
        chainInsP A M M' (p + 1 + r) (q + 1 + s) =
      (α_ M'.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M'
        (by omega : p + 1 + 1 + r = p + 1 + r + 1)
        (by omega : q + 1 + s = q + 1 + s) := by
  have hp₀ : p + 1 + 1 + r = p + 1 + r + 1 := by omega
  have hq₀ : q + 1 + s = q + 1 + s := rfl
  refine (cancel_epi (M'.X ◁
    (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
      modTensorπ A (symPowMod A M'.X r)
        (symPowMod A M.X s)))).mp ?_
  show (M'.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((M'.X ◁ chainMul2 A M M' p q r s) ≫
        chainInsP A M M' (p + 1 + r) (q + 1 + s)) =
    (M'.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((α_ M'.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M'
        (by omega : p + 1 + 1 + r = p + 1 + r + 1)
        (by omega : q + 1 + s = q + 1 + s))
  -- The left leg: merge the pair cover into the multiplication,
  -- fire its defining equation, and absorb the insertion's
  -- defining equation at the merged arity.
  have l1 : (M'.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((M'.X ◁ chainMul2 A M M' p q r s) ≫
        chainInsP A M M' (p + 1 + r) (q + 1 + s)) =
    (M'.X ◁
      ((modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
        chainMul2 A M M' p q r s)) ≫
      chainInsP A M M' (p + 1 + r) (q + 1 + s) := by
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  have l2 : (M'.X ◁
      ((modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
        chainMul2 A M M' p q r s)) ≫
      chainInsP A M M' (p + 1 + r) (q + 1 + s) =
    (M'.X ◁
      (tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))) ≫
      chainInsP A M M' (p + 1 + r) (q + 1 + s) :=
    congrArg (fun u :
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1)) ⊗
            (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s) =>
      (M'.X ◁ u) ≫ chainInsP A M M' (p + 1 + r) (q + 1 + s))
      (tensorHom_π_chainMul2 A M M' p q r s)
  have l3w1 : M'.X ◁
      (tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s))) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M'.X ◁
        ((symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))) :=
    MonoidalCategory.whiskerLeft_comp M'.X _ _
  have l3w2 : M'.X ◁
      ((symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s))) =
    (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      (M'.X ◁ modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))) :=
    MonoidalCategory.whiskerLeft_comp M'.X _ _
  have l3 : (M'.X ◁
      (tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))) ≫
      chainInsP A M M' (p + 1 + r) (q + 1 + s) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((M'.X ◁ modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))) ≫
        chainInsP A M M' (p + 1 + r) (q + 1 + s)) := by
    rw [l3w1, l3w2]
    simp only [Category.assoc]
  have l4 : (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((M'.X ◁ modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))) ≫
        chainInsP A M M' (p + 1 + r) (q + 1 + s)) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((α_ M'.X (symPow A M'.X (p + 1 + r + 1))
          (symPow A M.X (q + 1 + s + 1))).inv ≫
        (symInsL A M'.X (p + 1 + r) ▷
          symPow A M.X (q + 1 + s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
          (symPowMod A M.X (q + 1 + s))) :=
    congrArg (fun t :
        M'.X ⊗ (symPow A M'.X (p + 1 + r + 1) ⊗
            symPow A M.X (q + 1 + s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r + 1) (q + 1 + s) =>
      (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1))) ≫
        (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1))) ≫ t)
      (whiskerLeft_π_chainInsP A M M' (p + 1 + r) (q + 1 + s))
  have hα6 : (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
      symMul A M.X (q + 1) (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1 + r + 1))
        (symPow A M.X (q + 1 + s + 1))).inv =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) := by
    have h := associator_inv_naturality (𝟙 M'.X)
      (symMul A M'.X (p + 1) (r + 1))
      (symMul A M.X (q + 1) (s + 1))
    simp only [MonoidalCategory.id_tensorHom] at h
    exact h
  have l5 : (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M'.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((α_ M'.X (symPow A M'.X (p + 1 + r + 1))
          (symPow A M.X (q + 1 + s + 1))).inv ≫
        (symInsL A M'.X (p + 1 + r) ▷
          symPow A M.X (q + 1 + s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
          (symPowMod A M.X (q + 1 + s))) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      (symInsL A M'.X (p + 1 + r) ▷
        symPow A M.X (q + 1 + s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) := by
    rw [reassoc_of% hα6]
  have l6 : (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      (symInsL A M'.X (p + 1 + r) ▷
        symPow A M.X (q + 1 + s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ≫
        symInsL A M'.X (p + 1 + r)) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    exact congrArg (fun t : symPow A M.X (q + 1) ⊗
          symPow A M.X (s + 1) ⟶ symPow A M.X (q + 1 + s + 1) =>
      (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1))) ≫
        (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (((M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ≫
          symInsL A M'.X (p + 1 + r)) ⊗ₘ t) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
          (symPowMod A M.X (q + 1 + s)))
      (Category.comp_id (symMul A M.X (q + 1) (s + 1)))
  -- The right leg: cross the inserted module past the
  -- interchange and reassemble the same meeting form.
  have hα1 : (M'.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      (α_ M'.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) := by
    have h := associator_inv_naturality (𝟙 M'.X)
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q))
      (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s))
    simp only [MonoidalCategory.id_tensorHom] at h
    exact h
  have r1 : (M'.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((α_ M'.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀) =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    ((reassoc_of% hα1)
      ((chainInsP A M M' p q ▷ chainStage2 A M M' r s) ≫
        chainMul2 A M M' (p + 1) q r s ≫
        chainStage2Cast A M M' hp₀ hq₀)).trans
      (Category.assoc _ _ _)
  have r2 : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ≫ chainInsP A M M' p q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    congrArg (fun t :
        (M'.X ⊗ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))) ⊗
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r + 1) (q + 1 + s) =>
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        t)
      (tensorHom_whiskerRight_absorb
        (M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q))
        (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s))
        (chainInsP A M M' p q)
        (chainMul2 A M M' (p + 1) q r s ≫
          chainStage2Cast A M M' hp₀ hq₀))
  have r3 : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((M'.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ≫ chainInsP A M M' p q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    congrArg (fun t :
        M'.X ⊗ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1)) ⟶
          chainStage2 A M M' (p + 1) q =>
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (t ⊗ₘ modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
        chainMul2 A M M' (p + 1) q r s ≫
        chainStage2Cast A M M' hp₀ hq₀)
      (whiskerLeft_π_chainInsP A M M' p q)
  have r4 : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      (modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp]
    simp only [Category.assoc]
  have r5 : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      (modTensorπ A (symPowMod A M'.X (p + 1))
          (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' (p + 1) q r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1 + 1)) (symPow A M.X (q + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + 1 + r))
        (symPowMod A M.X (q + 1 + s)) ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    congrArg (fun t :
        (symPow A M'.X (p + 1 + 1) ⊗ symPow A M.X (q + 1)) ⊗
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r + 1) (q + 1 + s) =>
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (((α_ M'.X (symPow A M'.X (p + 1))
            (symPow A M.X (q + 1))).inv ≫
          (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
          𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫ t)
      (((reassoc_of%
          (tensorHom_π_chainMul2 A M M' (p + 1) q r s))
        (chainStage2Cast A M M' hp₀ hq₀)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (CategoryStruct.comp _)
            (Category.assoc _ _ _))))
  have hcast : modTensorπ A (symPowMod A M'.X (p + 1 + 1 + r))
      (symPowMod A M.X (q + 1 + s)) ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
      symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) :=
    modTensorπ_chainStage2Cast A M M' hp₀ hq₀
  have r6 : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1 + 1)) (symPow A M.X (q + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + 1 + r))
        (symPowMod A M.X (q + 1 + s)) ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1 + 1)) (symPow A M.X (q + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) :=
    congrArg (fun t :
        symPow A M'.X (p + 1 + 1 + r + 1) ⊗
          symPow A M.X (q + 1 + s + 1) ⟶
          chainStage2 A M M' (p + 1 + r + 1) (q + 1 + s) =>
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (((α_ M'.X (symPow A M'.X (p + 1))
            (symPow A M.X (q + 1))).inv ≫
          (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
          𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
        tensorμ (symPow A M'.X (p + 1 + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫ t)
      hcast
  have hpast : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1 + 1)) (symPow A M.X (q + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M'.X (r + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ⊗ₘ
        𝟙 (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) :=
    insL_past_tensorμ (symInsL A M'.X p)
  have r7 : (α_ M'.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M.X (q + 1))) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1 + 1)) (symPow A M.X (q + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M'.X (r + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ⊗ₘ
        𝟙 (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) := by
    rw [reassoc_of% hpast]
  have r8 : (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M'.X (r + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ⊗ₘ
        𝟙 (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (symMul A M'.X (p + 1 + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M'.X (r + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ≫
        symMul A M'.X (p + 1 + 1) (r + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ hp₀)) ⊗ₘ
        ((𝟙 (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1)) ≫
          symMul A M.X (q + 1) (s + 1)) ≫
          symPowCast A M.X (congrArg Nat.succ hq₀))) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  have h₁ : p + 1 + r + 2 = p + 2 + (r + 1) := by omega
  have hcc : symPowCast A M'.X h₁ ≫
      symPowCast A M'.X (congrArg Nat.succ hp₀) =
    𝟙 (symPow A M'.X (p + 1 + r + 2)) :=
    (symPowCast_symPowCast A M'.X h₁
      (congrArg Nat.succ hp₀)).trans rfl
  have hfacL : (((α_ M'.X (symPow A M'.X (p + 1))
        (symPow A M'.X (r + 1))).inv ≫
      (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ≫
      symMul A M'.X (p + 1 + 1) (r + 1)) ≫
      symPowCast A M'.X (congrArg Nat.succ hp₀) =
    (M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ≫
      symInsL A M'.X (p + 1 + r) := by
    show (((α_ M'.X (symPow A M'.X (p + 1))
        (symPow A M'.X (r + 1))).inv ≫
      (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ≫
      symMul A M'.X (p + 2) (r + 1)) ≫
      symPowCast A M'.X (congrArg Nat.succ hp₀) =
    (M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ≫
      symInsL A M'.X (p + 1 + r)
    simp only [Category.assoc]
    rw [reassoc_of% (symInsL_symMul A M'.X p r),
      Iso.inv_hom_id_assoc]
    exact congrArg (CategoryStruct.comp
      (M'.X ◁ symMul A M'.X (p + 1) (r + 1)))
      ((congrArg (CategoryStruct.comp
        (symInsL A M'.X (p + 1 + r))) hcc).trans
        (Category.comp_id _))
  have hfacR : (𝟙 (symPow A M.X (q + 1) ⊗
      symPow A M.X (s + 1)) ≫
      symMul A M.X (q + 1) (s + 1)) ≫
      symPowCast A M.X (congrArg Nat.succ hq₀) =
    symMul A M.X (q + 1) (s + 1) := by
    rw [Category.id_comp,
      show symPowCast A M.X (congrArg Nat.succ hq₀) =
        𝟙 (symPow A M.X (q + 1 + s + 1)) from rfl]
    exact Category.comp_id _
  have r9 : (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((((α_ M'.X (symPow A M'.X (p + 1))
          (symPow A M'.X (r + 1))).inv ≫
        (symInsL A M'.X p ▷ symPow A M'.X (r + 1))) ≫
        symMul A M'.X (p + 1 + 1) (r + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ hp₀)) ⊗ₘ
        ((𝟙 (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1)) ≫
          symMul A M.X (q + 1) (s + 1)) ≫
          symPowCast A M.X (congrArg Nat.succ hq₀))) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) =
    (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M'.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((M'.X ◁ symMul A M'.X (p + 1) (r + 1)) ≫
        symInsL A M'.X (p + 1 + r)) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
        (symPowMod A M.X (q + 1 + s)) :=
    congrArg (fun t :
        (M'.X ⊗ (symPow A M'.X (p + 1) ⊗
            symPow A M'.X (r + 1))) ⊗
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1)) ⟶
          symPow A M'.X (p + 1 + r + 1 + 1) ⊗
            symPow A M.X (q + 1 + s + 1) =>
      (M'.X ◁ tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1))) ≫
        (α_ M'.X (symPow A M'.X (p + 1) ⊗
            symPow A M'.X (r + 1))
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        t ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r + 1))
          (symPowMod A M.X (q + 1 + s)))
      (congrArg₂ (· ⊗ₘ ·) hfacL hfacR)
  exact (l1.trans (l2.trans (l3.trans (l4.trans
      (l5.trans l6))))).trans
    (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans
      (r6.trans (r7.trans (r8.trans r9)))))))).symm

/-- **The transition square for the first-slot insertion**: the
insertion passes the seed transition, raising the merged arities
by one on each side. -/
theorem chainInsP_delta2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (p q : ℕ) :
    (M'.X ◁ chainDelta2 A M M' d p q) ≫
        chainInsP A M M' (p + 1) (q + 1) =
      chainInsP A M M' p q ≫ chainDelta2 A M M' d (p + 1) q := by
  have hz : p + 1 + 1 + 0 = p + 1 + 0 + 1 := by omega
  have hz' : q + 1 + 0 = q + 1 + 0 := rfl
  -- The left leg: unfold the transition, distribute the whisker,
  -- pass the insertion through the stage multiplication, and
  -- absorb the trivial index transport.
  have l1 : (M'.X ◁ chainDelta2 A M M' d p q) ≫
      chainInsP A M M' (p + 1) (q + 1) =
    (M'.X ◁ ((ρ_ (chainStage2 A M M' p q)).inv ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0)) ≫
      chainInsP A M M' (p + 1) (q + 1) := rfl
  have w1 : M'.X ◁ ((ρ_ (chainStage2 A M M' p q)).inv ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0) =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainMul2 A M M' p q 0 0)) :=
    MonoidalCategory.whiskerLeft_comp M'.X _ _
  have w2 : M'.X ◁ (MonoidalCategory.whiskerLeft
      (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0) =
    (M'.X ◁ MonoidalCategory.whiskerLeft
      (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (M'.X ◁ chainMul2 A M M' p q 0 0) :=
    MonoidalCategory.whiskerLeft_comp M'.X _ _
  have l2 : (M'.X ◁ ((ρ_ (chainStage2 A M M' p q)).inv ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0)) ≫
      chainInsP A M M' (p + 1) (q + 1) =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((M'.X ◁ chainMul2 A M M' p q 0 0) ≫
        chainInsP A M M' (p + 1) (q + 1)) := by
    rw [w1, w2]
    simp only [Category.assoc]
  have l3 : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((M'.X ◁ chainMul2 A M M' p q 0 0) ≫
        chainInsP A M M' (p + 1 + 0) (q + 1 + 0)) =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M'.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        (chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0 ≫
        chainStage2Cast A M M' hz hz') :=
    congrArg (fun t : M'.X ⊗ (chainStage2 A M M' p q ⊗
          chainStage2 A M M' 0 0) ⟶
        chainStage2 A M M' (p + 1 + 0 + 1) (q + 1 + 0) =>
      (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (M'.X ◁ MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫ t)
      (chainInsP_mul A M M' p q 0 0)
  have hkill : chainMul2 A M M' (p + 1) q 0 0 ≫
      chainStage2Cast A M M' hz hz' =
    chainMul2 A M M' (p + 1) q 0 0 :=
    (congrArg
      (CategoryStruct.comp (chainMul2 A M M' (p + 1) q 0 0))
      (show chainStage2Cast A M M' hz hz' =
        𝟙 (chainStage2 A M M' (p + 1 + 1 + 0) (q + 1 + 0)) from
        rfl)).trans (Category.comp_id _)
  have l4 : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M'.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        (chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0 ≫
        chainStage2Cast A M M' hz hz') =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M'.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)) :=
    congrArg (fun t : chainStage2 A M M' (p + 1) q ⊗
          chainStage2 A M M' 0 0 ⟶
        chainStage2 A M M' (p + 1 + 0 + 1) (q + 1 + 0) =>
      (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (M'.X ◁ MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        ((α_ M'.X (chainStage2 A M M' p q)
            (chainStage2 A M M' 0 0)).inv ≫
          ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
            t)))
      hkill
  -- Unitor and seed bookkeeping, as in `chainDelta2_mul_right`.
  have hseed : (M'.X ◁ MonoidalCategory.whiskerLeft
      (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (α_ M'.X (chainStage2 A M M' p q)
        (chainStage2 A M M' 0 0)).inv =
    (α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
      MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) :=
    associator_inv_naturality_right _ _ _
  have hρ : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv := by
    monoidal
  have c1 : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M'.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)) =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
        (α_ M'.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv) ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)) :=
    congrArg
      (CategoryStruct.comp
        (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv))
      (Category.assoc _ _ _).symm
  have c2 : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((M'.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
        (α_ M'.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv) ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)) =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerLeft
          (M'.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)) :=
    congrArg (fun t : M'.X ⊗ (chainStage2 A M M' p q ⊗ 𝟙_ D) ⟶
        (M'.X ⊗ chainStage2 A M M' p q) ⊗
          chainStage2 A M M' 0 0 =>
      (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (t ≫ ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)))
      hseed
  have c3 : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerLeft
          (M'.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0)) =
    (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      ((α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        (MonoidalCategory.whiskerLeft
          (M'.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0))) :=
    congrArg
      (CategoryStruct.comp
        (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv))
      (Category.assoc _ _ _)
  have c4 : (M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      ((α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        (MonoidalCategory.whiskerLeft
          (M'.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) ≫
        ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' (p + 1) q 0 0))) =
    ((M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv) ≫
      (MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0)) :=
    (Category.assoc _ _ _).symm
  have c5 : ((M'.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ M'.X (chainStage2 A M M' p q) (𝟙_ D)).inv) ≫
      (MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0)) =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0)) :=
    congrArg (fun t : M'.X ⊗ chainStage2 A M M' p q ⟶
        (M'.X ⊗ chainStage2 A M M' p q) ⊗ 𝟙_ D =>
      t ≫ (MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0)))
      hρ
  -- The right leg: unfold the transition and slide the insertion
  -- past the unitor and the seed.
  have hρnat : chainInsP A M M' p q ≫
      (ρ_ (chainStage2 A M M' (p + 1) q)).inv =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (chainInsP A M M' p q ▷ 𝟙_ D) :=
    rightUnitor_inv_naturality _
  have hexch : (chainInsP A M M' p q ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) =
    MonoidalCategory.whiskerLeft
      (M'.X ⊗ chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) :=
    (whisker_exchange _ _).symm
  have b1 : chainInsP A M M' p q ≫
      chainDelta2 A M M' d (p + 1) q =
    chainInsP A M M' p q ≫
      ((ρ_ (chainStage2 A M M' (p + 1) q)).inv ≫
        (MonoidalCategory.whiskerLeft
          (chainStage2 A M M' (p + 1) q)
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainMul2 A M M' (p + 1) q 0 0)) := rfl
  have b2 : chainInsP A M M' p q ≫
      ((ρ_ (chainStage2 A M M' (p + 1) q)).inv ≫
        (MonoidalCategory.whiskerLeft
          (chainStage2 A M M' (p + 1) q)
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainMul2 A M M' (p + 1) q 0 0)) =
    (chainInsP A M M' p q ≫
      (ρ_ (chainStage2 A M M' (p + 1) q)).inv) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0) :=
    (Category.assoc _ _ _).symm
  have b3 : (chainInsP A M M' p q ≫
      (ρ_ (chainStage2 A M M' (p + 1) q)).inv) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0) =
    ((ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (chainInsP A M M' p q ▷ 𝟙_ D)) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0) :=
    congrArg (fun t : M'.X ⊗ chainStage2 A M M' p q ⟶
        chainStage2 A M M' (p + 1) q ⊗ 𝟙_ D =>
      t ≫ (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0))
      hρnat
  have b4 : ((ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (chainInsP A M M' p q ▷ 𝟙_ D)) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0) =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((chainInsP A M M' p q ▷ 𝟙_ D) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0)) :=
    Category.assoc _ _ _
  have b5 : (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((chainInsP A M M' p q ▷ 𝟙_ D) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' (p + 1) q 0 0)) =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (((chainInsP A M M' p q ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      chainMul2 A M M' (p + 1) q 0 0) :=
    congrArg
      (CategoryStruct.comp
        (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv)
      (Category.assoc _ _ _).symm
  have b6 : (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (((chainInsP A M M' p q ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (p + 1) q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      chainMul2 A M M' (p + 1) q 0 0) =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' 0 0)) ≫
      chainMul2 A M M' (p + 1) q 0 0) :=
    congrArg (fun t : (M'.X ⊗ chainStage2 A M M' p q) ⊗ 𝟙_ D ⟶
        chainStage2 A M M' (p + 1) q ⊗
          chainStage2 A M M' 0 0 =>
      (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
        (t ≫ chainMul2 A M M' (p + 1) q 0 0))
      hexch
  have b7 : (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (chainInsP A M M' p q ▷ chainStage2 A M M' 0 0)) ≫
      chainMul2 A M M' (p + 1) q 0 0) =
    (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv ≫
      (MonoidalCategory.whiskerLeft
        (M'.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsP A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' (p + 1) q 0 0)) :=
    congrArg
      (CategoryStruct.comp
        (ρ_ (M'.X ⊗ chainStage2 A M M' p q)).inv)
      (Category.assoc _ _ _)
  exact (l1.trans (l2.trans (l3.trans (l4.trans (c1.trans
      (c2.trans (c3.trans (c4.trans c5)))))))).trans
    (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans
      (b6.trans b7)))))).symm

end Ins2Laws

end RS
