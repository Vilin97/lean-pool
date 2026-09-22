/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainIns.FirstSlot

/-!
# The second-slot insertion against the stage structure

The mirror of [FirstSlot.lean](FirstSlot.lean) for the insertion
into the second slot of a two-index chain stage: the letter is
carried past the first slot by the braiding, so the crossings the
proofs need are established first.

* `chainInsQ_mul`: inserting a letter into a merged stage is
  inserting into the first factor's second slot and multiplying, up
  to the index transport.
* `chainInsQ_delta2`: the insertion passes the seed transition,
  raising the merged arities by one on each side.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Braided crossings for the second-slot insertion -/

section InsQCross

/-- A tensor pair passes the carried crossing of a letter: the
crossing is natural in the context and in the tail at once. -/
private theorem whiskerLeft_tensorHom_cross
    [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D]
    (X : D) {B B' T T' : D} (f : B ⟶ B') (g : T ⟶ T') :
    (X ◁ (f ⊗ₘ g)) ≫ (α_ X B' T').inv ≫
        ((β_ X B').hom ▷ T') ≫ (α_ B' X T').hom =
      (α_ X B T).inv ≫ ((β_ X B).hom ▷ T) ≫ (α_ B X T).hom ≫
        (f ⊗ₘ (X ◁ g)) := by
  have h : (X ◁ (f ⊗ₘ g)) ≫ (braidPast X B' T').hom =
      (braidPast X B T).hom ≫ (f ⊗ₘ (X ◁ g)) := by
    rw [tensorHom_def f g, tensorHom_def f (X ◁ g)]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [braidPast_natural_tail, braidPast_natural_context_assoc]
  simpa only [braidPast_hom, Category.assoc] using h

/-- The carried crossing of a letter into the second slot of the
first pair passes the interchange: crossing then interchanging is
interchanging then crossing the merged context. -/
private theorem cross_past_tensorμ [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D]
    (X P Q R S : D) :
    (α_ X (P ⊗ Q) (R ⊗ S)).inv ≫
        ((α_ X P Q).inv ▷ (R ⊗ S)) ≫
        (((β_ X P).hom ▷ Q) ▷ (R ⊗ S)) ≫
        ((α_ P X Q).hom ▷ (R ⊗ S)) ≫
        tensorμ P (X ⊗ Q) R S =
      (X ◁ tensorμ P Q R S) ≫
        (α_ X (P ⊗ R) (Q ⊗ S)).inv ≫
        ((β_ X (P ⊗ R)).hom ▷ (Q ⊗ S)) ≫
        (α_ (P ⊗ R) X (Q ⊗ S)).hom ≫
        ((P ⊗ R) ◁ (α_ X Q S).inv) := by
  have hgather : ((α_ X P Q).inv ▷ (R ⊗ S)) ≫
      (((β_ X P).hom ▷ Q) ▷ (R ⊗ S)) ≫
      ((α_ P X Q).hom ▷ (R ⊗ S)) =
    (braidPast X P Q).hom ▷ (R ⊗ S) := by
    simp only [braidPast_hom,
      MonoidalCategory.comp_whiskerRight]
  have hμ₁ : tensorμ P (X ⊗ Q) R S =
      (α_ P (X ⊗ Q) (R ⊗ S)).hom ≫
        (P ◁ (braidPast (X ⊗ Q) R S).hom) ≫
        (α_ P R ((X ⊗ Q) ⊗ S)).inv := by
    dsimp only [tensorμ]
    rw [braidPast_hom]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hμ₂ : tensorμ P Q R S =
      (α_ P Q (R ⊗ S)).hom ≫ (P ◁ (braidPast Q R S).hom) ≫
        (α_ P R (Q ⊗ S)).inv := by
    dsimp only [tensorμ]
    rw [braidPast_hom]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hfirst : (braidPast (X ⊗ Q) R S).hom =
      (α_ X Q (R ⊗ S)).hom ≫ (X ◁ (braidPast Q R S).hom) ≫
        (braidPast X R (Q ⊗ S)).hom ≫ (R ◁ (α_ X Q S).inv) := by
    rw [braidPast_hom]
    exact braidPast_tensor_first X Q R S
  have hctx : (α_ X (P ⊗ R) (Q ⊗ S)).inv ≫
      ((β_ X (P ⊗ R)).hom ▷ (Q ⊗ S)) ≫
      (α_ (P ⊗ R) X (Q ⊗ S)).hom =
    (X ◁ (α_ P R (Q ⊗ S)).hom) ≫
      (braidPast X P (R ⊗ Q ⊗ S)).hom ≫
      (P ◁ (braidPast X R (Q ⊗ S)).hom) ≫
      (α_ P R (X ⊗ Q ⊗ S)).inv := by
    rw [← cancel_mono (α_ P R (X ⊗ Q ⊗ S)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact braidPast_tensor_context X P R (Q ⊗ S)
  have hhead : (α_ X (P ⊗ Q) (R ⊗ S)).inv ≫
      ((braidPast X P Q).hom ▷ (R ⊗ S)) ≫
      (α_ P (X ⊗ Q) (R ⊗ S)).hom ≫
      (P ◁ (α_ X Q (R ⊗ S)).hom) =
    (X ◁ (α_ P Q (R ⊗ S)).hom) ≫
      (braidPast X P (Q ⊗ R ⊗ S)).hom := by
    simp only [braidPast_hom, MonoidalCategory.comp_whiskerRight,
      Category.assoc]
    monoidal
  have htail : (P ◁ (R ◁ (α_ X Q S).inv)) ≫
      (α_ P R ((X ⊗ Q) ⊗ S)).inv =
    (α_ P R (X ⊗ Q ⊗ S)).inv ≫ ((P ⊗ R) ◁ (α_ X Q S).inv) :=
    associator_inv_naturality_right P R (α_ X Q S).inv
  rw [reassoc_of% hgather, hμ₁, hfirst, hμ₂]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hhead, ← braidPast_natural_tail_assoc, htail,
    reassoc_of% hctx, whiskerLeft_inv_hom_assoc]

/-- An insertion into the first factor of the second pair, reached
by carrying the letter across the first factor, passes the
interchange. -/
private theorem crossIns_past_tensorμ [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D]
    {X P Q Q₂ R S : D} (f : X ⊗ Q ⟶ Q₂) :
    (α_ X (P ⊗ Q) (R ⊗ S)).inv ≫
        (((α_ X P Q).inv ≫ ((β_ X P).hom ▷ Q) ≫
          (α_ P X Q).hom ≫ (P ◁ f)) ⊗ₘ 𝟙 (R ⊗ S)) ≫
        tensorμ P Q₂ R S =
      (X ◁ tensorμ P Q R S) ≫
        (α_ X (P ⊗ R) (Q ⊗ S)).inv ≫
        ((β_ X (P ⊗ R)).hom ▷ (Q ⊗ S)) ≫
        (α_ (P ⊗ R) X (Q ⊗ S)).hom ≫
        (𝟙 (P ⊗ R) ⊗ₘ ((α_ X Q S).inv ≫ (f ▷ S))) := by
  have hnat := tensorμ_natural_left (𝟙 P) f R S
  simp only [MonoidalCategory.id_tensorHom,
    MonoidalCategory.id_whiskerRight] at hnat
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [hnat, reassoc_of% (cross_past_tensorμ X P Q R S)]

end InsQCross

section InsQSurgery

/-- Absorb a whiskered morphism into the second tensor factor. -/
private theorem tensorHom_whiskerLeft_absorb
    [Category.{v} D] [MonoidalCategory D]
    {X₁ X₂ Y₁ Y₂ Z₂ W : D} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (g : Y₂ ⟶ Z₂) (h : Y₁ ⊗ Z₂ ⟶ W) :
    (a ⊗ₘ b) ≫ (Y₁ ◁ g) ≫ h = (a ⊗ₘ (b ≫ g)) ≫ h := by
  rw [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id]

end InsQSurgery

section InsQ2Laws

/-- **The second-slot insertion passes the stage multiplication**:
inserting a letter into the merged stage is inserting into the
first factor's second slot and multiplying, up to the index
transport. -/
theorem chainInsQ_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q r s : ℕ) :
    (M.X ◁ chainMul2 A M M' p q r s) ≫
        chainInsQ A M M' (p + 1 + r) (q + 1 + s) =
      (α_ M.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M'
        (by omega : p + 1 + r = p + 1 + r)
        (by omega : q + 1 + 1 + s = q + 1 + s + 1) := by
  have hp₀ : p + 1 + r = p + 1 + r := rfl
  have hq₀ : q + 1 + 1 + s = q + 1 + s + 1 := by omega
  refine (cancel_epi (M.X ◁
    (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
      modTensorπ A (symPowMod A M'.X r)
        (symPowMod A M.X s)))).mp ?_
  show (M.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((M.X ◁ chainMul2 A M M' p q r s) ≫
        chainInsQ A M M' (p + 1 + r) (q + 1 + s)) =
    (M.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((α_ M.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M'
        (by omega : p + 1 + r = p + 1 + r)
        (by omega : q + 1 + 1 + s = q + 1 + s + 1))
  -- The left leg: merge the pair cover into the multiplication,
  -- fire its defining equation, and absorb the insertion's
  -- defining equation at the merged arity.
  have l1 : (M.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((M.X ◁ chainMul2 A M M' p q r s) ≫
        chainInsQ A M M' (p + 1 + r) (q + 1 + s)) =
    (M.X ◁
      ((modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
        chainMul2 A M M' p q r s)) ≫
      chainInsQ A M M' (p + 1 + r) (q + 1 + s) := by
    erw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  have l2 : (M.X ◁
      ((modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
        chainMul2 A M M' p q r s)) ≫
      chainInsQ A M M' (p + 1 + r) (q + 1 + s) =
    (M.X ◁
      (tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))) ≫
      chainInsQ A M M' (p + 1 + r) (q + 1 + s) :=
    congrArg (fun u :
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1)) ⊗
            (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s) =>
      (M.X ◁ u) ≫ chainInsQ A M M' (p + 1 + r) (q + 1 + s))
      (tensorHom_π_chainMul2 A M M' p q r s)
  have l3w1 : M.X ◁
      (tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s))) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M.X ◁
        ((symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))) :=
    MonoidalCategory.whiskerLeft_comp M.X _ _
  have l3w2 : M.X ◁
      ((symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s))) =
    (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      (M.X ◁ modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))) :=
    MonoidalCategory.whiskerLeft_comp M.X _ _
  have l3 : (M.X ◁
      (tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))) ≫
      chainInsQ A M M' (p + 1 + r) (q + 1 + s) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((M.X ◁ modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))) ≫
        chainInsQ A M M' (p + 1 + r) (q + 1 + s)) := by
    rw [l3w1, l3w2]
    repeat' erw [Category.assoc]
  have l4 : (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((M.X ◁ modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s))) ≫
        chainInsQ A M M' (p + 1 + r) (q + 1 + s)) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((α_ M.X (symPow A M'.X (p + 1 + r + 1))
          (symPow A M.X (q + 1 + s + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1 + r + 1))).hom ▷
          symPow A M.X (q + 1 + s + 1)) ≫
        (α_ (symPow A M'.X (p + 1 + r + 1)) M.X
          (symPow A M.X (q + 1 + s + 1))).hom ≫
        (symPow A M'.X (p + 1 + r + 1) ◁
          symInsL A M.X (q + 1 + s)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s + 1))) :=
    congrArg (fun t :
        M.X ⊗ (symPow A M'.X (p + 1 + r + 1) ⊗
            symPow A M.X (q + 1 + s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s + 1) =>
      (M.X ◁ tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1))) ≫
        (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1))) ≫ t)
      (whiskerLeft_π_chainInsQ A M M' (p + 1 + r) (q + 1 + s))
  have hβ6 : (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
      symMul A M.X (q + 1) (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1 + r + 1))
        (symPow A M.X (q + 1 + s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1 + r + 1))).hom ▷
        symPow A M.X (q + 1 + s + 1)) ≫
      (α_ (symPow A M'.X (p + 1 + r + 1)) M.X
        (symPow A M.X (q + 1 + s + 1))).hom =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        (M.X ◁ symMul A M.X (q + 1) (s + 1))) :=
    whiskerLeft_tensorHom_cross M.X _ _
  have l5 : (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (M.X ◁ (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1))) ≫
      ((α_ M.X (symPow A M'.X (p + 1 + r + 1))
          (symPow A M.X (q + 1 + s + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1 + r + 1))).hom ▷
          symPow A M.X (q + 1 + s + 1)) ≫
        (α_ (symPow A M'.X (p + 1 + r + 1)) M.X
          (symPow A M.X (q + 1 + s + 1))).hom ≫
        (symPow A M'.X (p + 1 + r + 1) ◁
          symInsL A M.X (q + 1 + s)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s + 1))) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        (M.X ◁ symMul A M.X (q + 1) (s + 1))) ≫
      (symPow A M'.X (p + 1 + r + 1) ◁
        symInsL A M.X (q + 1 + s)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) := by
    rw [reassoc_of% hβ6]
  have l6 : (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        (M.X ◁ symMul A M.X (q + 1) (s + 1))) ≫
      (symPow A M'.X (p + 1 + r + 1) ◁
        symInsL A M.X (q + 1 + s)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        ((M.X ◁ symMul A M.X (q + 1) (s + 1)) ≫
          symInsL A M.X (q + 1 + s))) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) :=
    congrArg (fun t :
        (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ⊗
            (M.X ⊗ (symPow A M.X (q + 1) ⊗
              symPow A M.X (s + 1))) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s + 1) =>
      (M.X ◁ tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1))) ≫
        (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1) ⊗
          symPow A M'.X (r + 1))).hom ▷
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
        (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        t)
      (tensorHom_whiskerLeft_absorb
        (symMul A M'.X (p + 1) (r + 1))
        (M.X ◁ symMul A M.X (q + 1) (s + 1))
        (symInsL A M.X (q + 1 + s))
        (modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s + 1))))
  -- The right leg: cross the inserted module past the
  -- interchange and reassemble the same meeting form.
  have hα1 : (M.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      (α_ M.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) := by
    have h := associator_inv_naturality (𝟙 M.X)
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q))
      (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s))
    simp only [MonoidalCategory.id_tensorHom] at h
    exact h
  have r1 : (M.X ◁
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s))) ≫
      ((α_ M.X (chainStage2 A M M' p q)
        (chainStage2 A M M' r s)).inv ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀) =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    by
      have h := congrArg (fun t => t ≫
          ((chainInsQ A M M' p q ▷ chainStage2 A M M' r s) ≫
            chainMul2 A M M' p (q + 1) r s ≫
            chainStage2Cast A M M' hp₀ hq₀)) hα1
      conv at h => lhs; erw [Category.assoc]
      conv at h => rhs; erw [Category.assoc]
      exact h
  have r2 : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' r s) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ≫ chainInsQ A M M' p q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    congrArg (fun t :
        (M.X ⊗ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))) ⊗
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s + 1) =>
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        t)
      (tensorHom_whiskerRight_absorb
        (M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q))
        (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s))
        (chainInsQ A M M' p q)
        (chainMul2 A M M' p (q + 1) r s ≫
          chainStage2Cast A M M' hp₀ hq₀))
  have r3 : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((M.X ◁ modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q)) ≫ chainInsQ A M M' p q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    congrArg (fun t :
        M.X ⊗ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1)) ⟶
          chainStage2 A M M' p (q + 1) =>
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (t ⊗ₘ modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
        chainMul2 A M M' p (q + 1) r s ≫
        chainStage2Cast A M M' hp₀ hq₀)
      (whiskerLeft_π_chainInsQ A M M' p q)
  have r4 : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q) ≫
        modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      (modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ := by
    erw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp]
    repeat' erw [Category.assoc]
  have r5 : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      (modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X (q + 1)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r)
          (symPowMod A M.X s)) ≫
      chainMul2 A M M' p (q + 1) r s ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1 + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1 + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + 1 + s)) ≫
      chainStage2Cast A M M' hp₀ hq₀ :=
    congrArg (fun t :
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1 + 1)) ⊗
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1)) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s + 1) =>
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (((α_ M.X (symPow A M'.X (p + 1))
            (symPow A M.X (q + 1))).inv ≫
          ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
            symPow A M.X (q + 1)) ≫
          (α_ (symPow A M'.X (p + 1)) M.X
            (symPow A M.X (q + 1))).hom ≫
          (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
          𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫ t)
      (by
        have h := congrArg (fun t => t ≫ chainStage2Cast A M M' hp₀ hq₀)
          (tensorHom_π_chainMul2 A M M' p (q + 1) r s)
        conv at h => lhs; erw [Category.assoc]
        conv at h => rhs; erw [Category.assoc]; arg 2; erw [Category.assoc]
        exact h)
  have hcast : modTensorπ A (symPowMod A M'.X (p + 1 + r))
      (symPowMod A M.X (q + 1 + 1 + s)) ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
      symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) :=
    modTensorπ_chainStage2Cast A M M' hp₀ hq₀
  have r6 : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1 + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1 + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + 1 + s)) ≫
      chainStage2Cast A M M' hp₀ hq₀ =
    (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
        (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1 + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1 + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) :=
    congrArg (fun t :
        symPow A M'.X (p + 1 + r + 1) ⊗
          symPow A M.X (q + 1 + 1 + s + 1) ⟶
          chainStage2 A M M' (p + 1 + r) (q + 1 + s + 1) =>
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        (((α_ M.X (symPow A M'.X (p + 1))
            (symPow A M.X (q + 1))).inv ≫
          ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
            symPow A M.X (q + 1)) ≫
          (α_ (symPow A M'.X (p + 1)) M.X
            (symPow A M.X (q + 1))).hom ≫
          (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
          𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
        tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1 + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1 + 1) (s + 1)) ≫ t)
      hcast
  have hpast : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1 + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (𝟙 (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ⊗ₘ
        ((α_ M.X (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).inv ≫
          (symInsL A M.X q ▷ symPow A M.X (s + 1)))) :=
    crossIns_past_tensorμ (symInsL A M.X q)
  have r7 : (α_ M.X
      (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
      (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      (((α_ M.X (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1))).hom ▷
          symPow A M.X (q + 1)) ≫
        (α_ (symPow A M'.X (p + 1)) M.X
          (symPow A M.X (q + 1))).hom ≫
        (symPow A M'.X (p + 1) ◁ symInsL A M.X q)) ⊗ₘ
        𝟙 (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))) ≫
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1 + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1 + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (𝟙 (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ⊗ₘ
        ((α_ M.X (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).inv ≫
          (symInsL A M.X q ▷ symPow A M.X (s + 1)))) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1 + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) := by
    rw [reassoc_of% hpast]
  have r8 : (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (𝟙 (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ⊗ₘ
        ((α_ M.X (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).inv ≫
          (symInsL A M.X q ▷ symPow A M.X (s + 1)))) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1 + 1) (s + 1)) ≫
      (symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (((𝟙 (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ≫
          symMul A M'.X (p + 1) (r + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ hp₀)) ⊗ₘ
        ((((α_ M.X (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).inv ≫
          (symInsL A M.X q ▷ symPow A M.X (s + 1))) ≫
          symMul A M.X (q + 1 + 1) (s + 1)) ≫
          symPowCast A M.X (congrArg Nat.succ hq₀))) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) := by
    erw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  have h₁ : q + 1 + s + 2 = q + 2 + (s + 1) := by omega
  have hcc : symPowCast A M.X h₁ ≫
      symPowCast A M.X (congrArg Nat.succ hq₀) =
    𝟙 (symPow A M.X (q + 1 + s + 2)) :=
    (symPowCast_symPowCast A M.X h₁
      (congrArg Nat.succ hq₀)).trans rfl
  have hfacL : (𝟙 (symPow A M'.X (p + 1) ⊗
      symPow A M'.X (r + 1)) ≫
      symMul A M'.X (p + 1) (r + 1)) ≫
      symPowCast A M'.X (congrArg Nat.succ hp₀) =
    symMul A M'.X (p + 1) (r + 1) := by
    rw [Category.id_comp,
      show symPowCast A M'.X (congrArg Nat.succ hp₀) =
        𝟙 (symPow A M'.X (p + 1 + r + 1)) from rfl]
    exact Category.comp_id _
  have hfacR : ((((α_ M.X (symPow A M.X (q + 1))
        (symPow A M.X (s + 1))).inv ≫
      (symInsL A M.X q ▷ symPow A M.X (s + 1))) ≫
      symMul A M.X (q + 1 + 1) (s + 1)) ≫
      symPowCast A M.X (congrArg Nat.succ hq₀)) =
    (M.X ◁ symMul A M.X (q + 1) (s + 1)) ≫
      symInsL A M.X (q + 1 + s) := by
    show ((((α_ M.X (symPow A M.X (q + 1))
        (symPow A M.X (s + 1))).inv ≫
      (symInsL A M.X q ▷ symPow A M.X (s + 1))) ≫
      symMul A M.X (q + 2) (s + 1)) ≫
      symPowCast A M.X (congrArg Nat.succ hq₀)) =
    (M.X ◁ symMul A M.X (q + 1) (s + 1)) ≫
      symInsL A M.X (q + 1 + s)
    conv_lhs => erw [Category.assoc, Category.assoc]
    erw [reassoc_of% (symInsL_symMul A M.X q s),
      Iso.inv_hom_id_assoc]
    exact congrArg (CategoryStruct.comp
      (M.X ◁ symMul A M.X (q + 1) (s + 1)))
      ((congrArg (CategoryStruct.comp
        (symInsL A M.X (q + 1 + s))) hcc).trans
        (Category.comp_id _))
  have r9 : (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (((𝟙 (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ≫
          symMul A M'.X (p + 1) (r + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ hp₀)) ⊗ₘ
        ((((α_ M.X (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).inv ≫
          (symInsL A M.X q ▷ symPow A M.X (s + 1))) ≫
          symMul A M.X (q + 1 + 1) (s + 1)) ≫
          symPowCast A M.X (congrArg Nat.succ hq₀))) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) =
    (M.X ◁ tensorμ (symPow A M'.X (p + 1))
        (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
        (symPow A M.X (s + 1))) ≫
      (α_ M.X (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
      ((β_ M.X (symPow A M'.X (p + 1) ⊗
        symPow A M'.X (r + 1))).hom ▷
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
      (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) M.X
        (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        ((M.X ◁ symMul A M.X (q + 1) (s + 1)) ≫
          symInsL A M.X (q + 1 + s))) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s + 1)) :=
    congrArg (fun t :
        (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1)) ⊗
            (M.X ⊗ (symPow A M.X (q + 1) ⊗
              symPow A M.X (s + 1))) ⟶
          symPow A M'.X (p + 1 + r + 1) ⊗
            symPow A M.X (q + 1 + s + 1 + 1) =>
      (M.X ◁ tensorμ (symPow A M'.X (p + 1))
          (symPow A M.X (q + 1)) (symPow A M'.X (r + 1))
          (symPow A M.X (s + 1))) ≫
        (α_ M.X (symPow A M'.X (p + 1) ⊗
            symPow A M'.X (r + 1))
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).inv ≫
        ((β_ M.X (symPow A M'.X (p + 1) ⊗
          symPow A M'.X (r + 1))).hom ▷
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))) ≫
        (α_ (symPow A M'.X (p + 1) ⊗ symPow A M'.X (r + 1))
          M.X
          (symPow A M.X (q + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        t ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s + 1)))
      (congrArg₂ (· ⊗ₘ ·) hfacL hfacR)
  exact (l1.trans (l2.trans (l3.trans (l4.trans
      (l5.trans l6))))).trans
    (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans
      (r6.trans (r7.trans (r8.trans r9)))))))).symm

/-- **The transition square for the second-slot insertion**: the
insertion passes the seed transition, raising the merged arities
by one on each side. -/
theorem chainInsQ_delta2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (p q : ℕ) :
    (M.X ◁ chainDelta2 A M M' d p q) ≫
        chainInsQ A M M' (p + 1) (q + 1) =
      chainInsQ A M M' p q ≫ chainDelta2 A M M' d p (q + 1) := by
  have hz : p + 1 + 0 = p + 1 + 0 := rfl
  have hz' : q + 1 + 1 + 0 = q + 1 + 0 + 1 := by omega
  -- The left leg: unfold the transition, distribute the whisker,
  -- pass the insertion through the stage multiplication, and
  -- absorb the trivial index transport.
  have l1 : (M.X ◁ chainDelta2 A M M' d p q) ≫
      chainInsQ A M M' (p + 1) (q + 1) =
    (M.X ◁ ((ρ_ (chainStage2 A M M' p q)).inv ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0)) ≫
      chainInsQ A M M' (p + 1) (q + 1) := rfl
  have w1 : M.X ◁ ((ρ_ (chainStage2 A M M' p q)).inv ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0) =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainMul2 A M M' p q 0 0)) :=
    MonoidalCategory.whiskerLeft_comp M.X _ _
  have w2 : M.X ◁ (MonoidalCategory.whiskerLeft
      (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0) =
    (M.X ◁ MonoidalCategory.whiskerLeft
      (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (M.X ◁ chainMul2 A M M' p q 0 0) :=
    MonoidalCategory.whiskerLeft_comp M.X _ _
  have l2 : (M.X ◁ ((ρ_ (chainStage2 A M M' p q)).inv ≫
      MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p q 0 0)) ≫
      chainInsQ A M M' (p + 1) (q + 1) =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((M.X ◁ chainMul2 A M M' p q 0 0) ≫
        chainInsQ A M M' (p + 1) (q + 1)) := by
    rw [w1, w2]
    repeat' erw [Category.assoc]
  have l3 : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((M.X ◁ chainMul2 A M M' p q 0 0) ≫
        chainInsQ A M M' (p + 1 + 0) (q + 1 + 0)) =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        (chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0 ≫
        chainStage2Cast A M M' hz hz') :=
    congrArg (fun t : M.X ⊗ (chainStage2 A M M' p q ⊗
          chainStage2 A M M' 0 0) ⟶
        chainStage2 A M M' (p + 1 + 0) (q + 1 + 0 + 1) =>
      (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (M.X ◁ MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫ t)
      (chainInsQ_mul A M M' p q 0 0)
  have hkill : chainMul2 A M M' p (q + 1) 0 0 ≫
      chainStage2Cast A M M' hz hz' =
    chainMul2 A M M' p (q + 1) 0 0 :=
    (congrArg
      (CategoryStruct.comp (chainMul2 A M M' p (q + 1) 0 0))
      (show chainStage2Cast A M M' hz hz' =
        𝟙 (chainStage2 A M M' (p + 1 + 0) (q + 1 + 1 + 0)) from
        rfl)).trans (Category.comp_id _)
  have l4 : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        (chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0 ≫
        chainStage2Cast A M M' hz hz') =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)) :=
    congrArg (fun t : chainStage2 A M M' p (q + 1) ⊗
          chainStage2 A M M' 0 0 ⟶
        chainStage2 A M M' (p + 1 + 0) (q + 1 + 0 + 1) =>
      (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (M.X ◁ MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        ((α_ M.X (chainStage2 A M M' p q)
            (chainStage2 A M M' 0 0)).inv ≫
          ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
            t)))
      hkill
  -- Unitor and seed bookkeeping, as in `chainInsP_delta2`.
  have hseed : (M.X ◁ MonoidalCategory.whiskerLeft
      (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (α_ M.X (chainStage2 A M M' p q)
        (chainStage2 A M M' 0 0)).inv =
    (α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
      MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) :=
    associator_inv_naturality_right _ _ _
  have hρ : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv := by
    monoidal
  have c1 : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      ((α_ M.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)) =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
        (α_ M.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv) ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)) :=
    congrArg
      (CategoryStruct.comp
        (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv))
      (Category.assoc _ _ _).symm
  have c2 : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((M.X ◁ MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
        (α_ M.X (chainStage2 A M M' p q)
          (chainStage2 A M M' 0 0)).inv) ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)) =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerLeft
          (M.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)) :=
    congrArg (fun t : M.X ⊗ (chainStage2 A M M' p q ⊗ 𝟙_ D) ⟶
        (M.X ⊗ chainStage2 A M M' p q) ⊗
          chainStage2 A M M' 0 0 =>
      (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
        (t ≫ ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)))
      hseed
  have c3 : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (((α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        MonoidalCategory.whiskerLeft
          (M.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d)) ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0)) =
    (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      ((α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        (MonoidalCategory.whiskerLeft
          (M.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0))) :=
    congrArg
      (CategoryStruct.comp
        (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv))
      (Category.assoc _ _ _)
  have c4 : (M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      ((α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv ≫
        (MonoidalCategory.whiskerLeft
          (M.X ⊗ chainStage2 A M M' p q)
          (Y₂ := chainStage2 A M M' 0 0)
          (chainSeed A M M' d) ≫
        ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
          chainMul2 A M M' p (q + 1) 0 0))) =
    ((M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv) ≫
      (MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0)) :=
    (Category.assoc _ _ _).symm
  have c5 : ((M.X ◁ (ρ_ (chainStage2 A M M' p q)).inv) ≫
      (α_ M.X (chainStage2 A M M' p q) (𝟙_ D)).inv) ≫
      (MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0)) =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0)) :=
    congrArg (fun t : M.X ⊗ chainStage2 A M M' p q ⟶
        (M.X ⊗ chainStage2 A M M' p q) ⊗ 𝟙_ D =>
      t ≫ (MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0)))
      hρ
  -- The right leg: unfold the transition and slide the insertion
  -- past the unitor and the seed.
  have hρnat : chainInsQ A M M' p q ≫
      (ρ_ (chainStage2 A M M' p (q + 1))).inv =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (chainInsQ A M M' p q ▷ 𝟙_ D) :=
    rightUnitor_inv_naturality _
  have hexch : (chainInsQ A M M' p q ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) =
    MonoidalCategory.whiskerLeft
      (M.X ⊗ chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) :=
    (whisker_exchange _ _).symm
  have b1 : chainInsQ A M M' p q ≫
      chainDelta2 A M M' d p (q + 1) =
    chainInsQ A M M' p q ≫
      ((ρ_ (chainStage2 A M M' p (q + 1))).inv ≫
        (MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p (q + 1))
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainMul2 A M M' p (q + 1) 0 0)) := rfl
  have b2 : chainInsQ A M M' p q ≫
      ((ρ_ (chainStage2 A M M' p (q + 1))).inv ≫
        (MonoidalCategory.whiskerLeft
          (chainStage2 A M M' p (q + 1))
          (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
        chainMul2 A M M' p (q + 1) 0 0)) =
    (chainInsQ A M M' p q ≫
      (ρ_ (chainStage2 A M M' p (q + 1))).inv) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0) :=
    (Category.assoc _ _ _).symm
  have b3 : (chainInsQ A M M' p q ≫
      (ρ_ (chainStage2 A M M' p (q + 1))).inv) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0) =
    ((ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (chainInsQ A M M' p q ▷ 𝟙_ D)) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0) :=
    congrArg (fun t : M.X ⊗ chainStage2 A M M' p q ⟶
        chainStage2 A M M' p (q + 1) ⊗ 𝟙_ D =>
      t ≫ (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0))
      hρnat
  have b4 : ((ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (chainInsQ A M M' p q ▷ 𝟙_ D)) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0) =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((chainInsQ A M M' p q ▷ 𝟙_ D) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0)) :=
    Category.assoc _ _ _
  have b5 : (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((chainInsQ A M M' p q ▷ 𝟙_ D) ≫
      (MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      chainMul2 A M M' p (q + 1) 0 0)) =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (((chainInsQ A M M' p q ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      chainMul2 A M M' p (q + 1) 0 0) :=
    congrArg
      (CategoryStruct.comp
        (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv)
      (Category.assoc _ _ _).symm
  have b6 : (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (((chainInsQ A M M' p q ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' p (q + 1))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      chainMul2 A M M' p (q + 1) 0 0) =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0)) ≫
      chainMul2 A M M' p (q + 1) 0 0) :=
    congrArg (fun t : (M.X ⊗ chainStage2 A M M' p q) ⊗ 𝟙_ D ⟶
        chainStage2 A M M' p (q + 1) ⊗
          chainStage2 A M M' 0 0 =>
      (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
        (t ≫ chainMul2 A M M' p (q + 1) 0 0))
      hexch
  have b7 : (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      ((MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      (chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0)) ≫
      chainMul2 A M M' p (q + 1) 0 0) =
    (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv ≫
      (MonoidalCategory.whiskerLeft
        (M.X ⊗ chainStage2 A M M' p q)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
      ((chainInsQ A M M' p q ▷ chainStage2 A M M' 0 0) ≫
        chainMul2 A M M' p (q + 1) 0 0)) :=
    congrArg
      (CategoryStruct.comp
        (ρ_ (M.X ⊗ chainStage2 A M M' p q)).inv)
      (Category.assoc _ _ _)
  exact (l1.trans (l2.trans (l3.trans (l4.trans (c1.trans
      (c2.trans (c3.trans (c4.trans c5)))))))).trans
    (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans
      (b6.trans b7)))))).symm

end InsQ2Laws

end RS
