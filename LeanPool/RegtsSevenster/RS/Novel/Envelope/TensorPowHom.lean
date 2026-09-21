/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPerm

/-!
# The tensor power of an endomorphism

An endomorphism `g` of `X` induces an endomorphism of the tensor
power `X ^ ⊗ n`, one copy of `g` acting on each factor (`powHom`).
It commutes with the symmetric-group action of `SymPerm.lean`:
every factor carries the same endomorphism, so permuting the factors
and applying `g` to each may be done in either order
(`permMor_comp_powHom`).
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-! ## The tensor power of an endomorphism -/

/-- **The tensor power of an endomorphism**: `powHom X g n` acts by
`g` on each of the `n` factors of `X ^ ⊗ n`. -/
noncomputable def powHom [Category.{v} A] [MonoidalCategory A]
    (X : A) (g : End X) :
    (n : ℕ) → End (tensorPow A X n)
  | 0 => 𝟙 _
  | n + 1 => powHom X g n ⊗ₘ g

/-- On the empty tensor power the endomorphism power is the
identity of the unit. -/
@[simp]
theorem powHom_zero [Category.{v} A] [MonoidalCategory A]
    (X : A) (g : End X) :
    powHom X g 0 = 𝟙 (𝟙_ A) := rfl

/-- The recursion equation: the endomorphism power on one more
factor tensors on one more copy of `g`. -/
@[simp]
theorem powHom_succ [Category.{v} A] [MonoidalCategory A]
    (X : A) (g : End X) (n : ℕ) :
    powHom X g (n + 1) = powHom X g n ⊗ₘ g := rfl

/-! ## Commutation with whiskering -/

/-- A composite of two morphisms that each commute with a third
commutes with it.  Stated at a general object, so that no
tensor-power arity enters the rewriting. -/
private theorem comp_comm [Category.{v} A]
    {P : A} {s t p : P ⟶ P}
    (hs : s ≫ p = p ≫ s) (ht : t ≫ p = p ≫ t) :
    (s ≫ t) ≫ p = p ≫ s ≫ t := by
  rw [Category.assoc, ht, ← Category.assoc, hs, Category.assoc]

/-- Whiskering against a factorwise endomorphism: a morphism that
commutes with `p` commutes with `p ⊗ₘ a` once whiskered.  Stated at
general objects, so that no tensor-power arity enters the
rewriting. -/
private theorem whisker_tensor_comm [Category.{v} A] [MonoidalCategory A]
    {P X : A} {f p : P ⟶ P}
    {a : X ⟶ X} (h : f ≫ p = p ≫ f) :
    (f ▷ X) ≫ (p ⊗ₘ a) = (p ⊗ₘ a) ≫ (f ▷ X) := by
  rw [MonoidalCategory.whiskerRight_comp_tensorHom, h,
    ← MonoidalCategory.tensorHom_comp_whiskerRight]

/-- Adding a factor preserves commutation with the endomorphism
power. -/
theorem whiskerRight_comp_powHom [Category.{v} A] [MonoidalCategory A]
    (X : A) (g : End X) (n : ℕ)
    (f : tensorPow A X n ⟶ tensorPow A X n)
    (h : f ≫ powHom X g n = powHom X g n ≫ f) :
    (f ▷ X) ≫ powHom X g (n + 1) =
      powHom X g (n + 1) ≫ (f ▷ X) :=
  whisker_tensor_comm h

/-! ## Equivariance -/

/-- The braiding of the top two tensorands, conjugated by the
associator, exchanges the top two components of a factorwise
endomorphism.  Stated at general objects, so that no tensor-power
arity enters the rewriting. -/
private theorem tensor_swap_comm
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {P X Y : A} (p : P ⟶ P) (a : X ⟶ X)
    (b : Y ⟶ Y) :
    ((p ⊗ₘ a) ⊗ₘ b) ≫
        ((α_ P X Y).hom ≫ (P ◁ (β_ X Y).hom) ≫ (α_ P Y X).inv) =
      ((α_ P X Y).hom ≫ (P ◁ (β_ X Y).hom) ≫ (α_ P Y X).inv) ≫
        ((p ⊗ₘ b) ⊗ₘ a) := by
  rw [MonoidalCategory.associator_naturality_assoc,
    MonoidalCategory.tensorHom_comp_whiskerLeft_assoc,
    BraidedCategory.braiding_naturality,
    ← MonoidalCategory.whiskerLeft_comp_tensorHom_assoc,
    MonoidalCategory.associator_inv_naturality]
  simp only [Category.assoc]

/-- The top braiding commutes with the endomorphism power: the two
braided factors carry the same endomorphism. -/
theorem swapTop_comp_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (g : End X) (n : ℕ) :
    swapTop X n ≫ powHom X g (n + 2) =
      powHom X g (n + 2) ≫ swapTop X n :=
  (tensor_swap_comm (powHom X g n) g g).symm

/-- Bubbling the top factor down commutes with the endomorphism
power, one braiding step at a time. -/
theorem insertTop_comp_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (g : End X) :
    ∀ (n k : ℕ), insertTop X n k ≫ powHom X g (n + 1) =
      powHom X g (n + 1) ≫ insertTop X n k
  | n, 0 => by
      rw [insertTop_zero, Category.id_comp, Category.comp_id]
  | 0, _ + 1 => by
      rw [insertTop_of_zero, Category.id_comp, Category.comp_id]
  | n + 1, k + 1 => by
      rw [insertTop_succ]
      exact comp_comm (swapTop_comp_powHom X g n)
        (whiskerRight_comp_powHom X g (n + 1) (insertTop X n k)
          (insertTop_comp_powHom X g n k))

/-- **Equivariance of the endomorphism power**: the symmetric-group
action commutes with `g ^ ⊗ n`.  Every factor carries the same
endomorphism, so permuting the factors and applying `g` to each may
be done in either order. -/
theorem permMor_comp_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (g : End X) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permMor X n σ ≫ powHom X g n = powHom X g n ≫ permMor X n σ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [permMor_succ]
    exact comp_comm
      (whiskerRight_comp_powHom X g n (permMor X n (restPerm σ))
        (ih (restPerm σ)))
      (insertTop_comp_powHom X g n (n - (topImage σ : ℕ)))

end RS
