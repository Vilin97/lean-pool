/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.TensorPowHom
import LeanPool.RegtsSevenster.RS.Classical.CatTheory.PartialTrace

/-!
# The trace of a cycle against a tensor power

The trace of the insertion cycle against the tensor power of an
endomorphism: bubbling the top factor down `k` slots and letting
`g` act on every factor traces to `tr(g ^ (k + 1))` times `tr g` on
each of the untouched factors.

The argument descends one arity at a time.  Tracing out the top
factor turns the bubbling at arity `n + 1` into the bubbling at
arity `n` preceded by one more copy of `g` on the new top factor —
the partial trace of the braiding is the identity — and the full
trace is unchanged by the descent (`catTrace_ptr`).  Carrying an
arbitrary endomorphism on the top factor through the induction is
what makes the accumulated copies of `g` bookkeepable.
-/

namespace RS

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory

universe v u

variable {A : Type u}

/-! ## The trace of a tensor power -/

/-- **The trace of a tensor power** of an endomorphism is the power
of its trace. -/
theorem catTrace_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) :
    ∀ n : ℕ, catTrace (powHom X g n) = catTrace g ^ n
  | 0 => by
      change catTrace (𝟙 (𝟙_ A)) = catTrace g ^ 0
      rw [catTrace_id, catDim_unit, pow_zero]
  | n + 1 => by
      change catTrace (powHom X g n ⊗ₘ g) = catTrace g ^ (n + 1)
      rw [catTrace_tensorHom, catTrace_powHom X g n, pow_succ]

/-! ## Bubbling one slot down -/

/-- The top factor's endomorphism passes the top braiding onto the
factor below it. -/
private theorem whiskerLeft_swapTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (Q X : A) (h : X ⟶ X) :
    ((Q ⊗ X) ◁ h) ≫
        ((α_ Q X X).hom ≫ (Q ◁ (β_ X X).hom) ≫ (α_ Q X X).inv) =
      ((α_ Q X X).hom ≫ (Q ◁ (β_ X X).hom) ≫ (α_ Q X X).inv) ≫
        ((Q ◁ h) ▷ X) := by
  have hleft : (Q ⊗ X) ◁ h =
      (α_ Q X X).hom ≫ (Q ◁ (X ◁ h)) ≫ (α_ Q X X).inv := by
    rw [← Category.assoc, ← associator_naturality_right,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hright : (Q ◁ h) ▷ X =
      (α_ Q X X).hom ≫ (Q ◁ (h ▷ X)) ≫ (α_ Q X X).inv := by
    rw [← Category.assoc, whisker_assoc, Category.assoc]
  rw [hleft, hright]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (Q ◁ (X ◁ h)), ← whiskerLeft_comp,
    braiding_naturality_right, whiskerLeft_comp, Category.assoc]

/-- **One step of the descent**, at general objects.  Tracing out
the top factor of a braiding followed by a morphism of the factors
below it and a tensor power leaves the same data one arity down,
with the two endomorphisms of the traced factor composed onto the
factor that remains. -/
private theorem ptr_cycle_step
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (Q X : A) (g h : X ⟶ X)
    (v a : Q ⊗ X ⟶ Q ⊗ X) :
    ptr (((Q ⊗ X) ◁ h) ≫
        ((α_ Q X X).hom ≫ (Q ◁ (β_ X X).hom) ≫ (α_ Q X X).inv) ≫
        (v ▷ X) ≫ (a ⊗ₘ g)) =
      (Q ◁ (g ≫ h)) ≫ v ≫ a := by
  have hswap := whiskerLeft_swapTop Q X h
  have htensor : (a ⊗ₘ g) = ((Q ⊗ X) ◁ g) ≫ (a ▷ X) :=
    tensorHom_def' a g
  rw [← Category.assoc, hswap, htensor]
  simp only [Category.assoc]
  rw [← Category.assoc ((Q ◁ h) ▷ X), ← comp_whiskerRight,
    ← Category.assoc (((Q ◁ h) ≫ v) ▷ X),
    ← whisker_exchange, Category.assoc, ← comp_whiskerRight,
    ← Category.assoc ((α_ Q X X).hom), ← Category.assoc,
    ← Category.assoc, ptr_comp_whiskerRight]
  have hbr := ptr_braiding_whiskerLeft Q X g
  simp only [Category.assoc] at hbr ⊢
  rw [hbr, ← Category.assoc, ← whiskerLeft_comp]

/-- The descent step at a tensor power, where the braiding is
`swapTop`. -/
private theorem ptr_cycle_step_swapTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g h : End X) (m : ℕ)
    (v a : tensorPow A X (m + 1) ⟶ tensorPow A X (m + 1)) :
    ptr ((tensorPow A X (m + 1) ◁ h) ≫ swapTop X m ≫ (v ▷ X) ≫
        (a ⊗ₘ g)) =
      (tensorPow A X m ◁ (g ≫ h)) ≫ v ≫ a :=
  ptr_cycle_step (tensorPow A X m) X g h v a

/-- Composing one more copy on the right of a power. -/
private theorem pow_comp_self [Category.{v} A]
    {X : A} (g : End X) (k : ℕ) :
    (g ^ (k + 1)) ≫ g = g ^ (k + 2) := by
  change (g ^ (k + 1)) ≫ g = g ^ (k + 1 + 1)
  rw [pow_succ' g (k + 1)]
  exact (End.mul_def g (g ^ (k + 1))).symm

/-! ## The cycle trace -/

/-- **The trace of the insertion cycle against a tensor power.**
Bubbling the top factor down `k` slots and letting `g` act on every
factor, with a further endomorphism `h` on the top factor, traces to
`tr (h ∘ g ^ (k + 1))` times one copy of `tr g` for each factor the
bubbling does not reach. -/
theorem catTrace_insertTop_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) :
    ∀ (k n : ℕ), k ≤ n → ∀ h : End X,
      catTrace ((tensorPow A X n ◁ h) ≫
          insertTop X n k ≫ powHom X g (n + 1)) =
        catTrace g ^ (n - k) * catTrace (h ≫ (g ^ (k + 1)))
  | 0, n, _, h => by
      have hz : (tensorPow A X n ◁ h) ≫
          insertTop X n 0 ≫ powHom X g (n + 1) =
          powHom X g n ⊗ₘ (h ≫ g) := by
        rw [insertTop_zero]
        change (tensorPow A X n ◁ h) ≫ 𝟙 _ ≫ (powHom X g n ⊗ₘ g) = _
        rw [Category.id_comp, ← id_tensorHom,
          tensorHom_comp_tensorHom, Category.id_comp]
      refine (congrArg catTrace hz).trans ?_
      rw [catTrace_tensorHom, catTrace_powHom, Nat.sub_zero, pow_one]
  | k + 1, n, hk, h => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hkm : k ≤ m := by omega
      have hmor : (tensorPow A X (m + 1) ◁ h) ≫
            insertTop X (m + 1) (k + 1) ≫ powHom X g (m + 1 + 1) =
          (tensorPow A X (m + 1) ◁ h) ≫ swapTop X m ≫
            (insertTop X m k ▷ X) ≫ (powHom X g (m + 1) ⊗ₘ g) := by
        rw [insertTop_succ, powHom_succ]
        exact congrArg (fun z => (tensorPow A X (m + 1) ◁ h) ≫ z)
          (Category.assoc _ _ _)
      refine (catTrace_ptr _).symm.trans ?_
      refine (congrArg (fun z => catTrace (ptr z)) hmor).trans ?_
      rw [ptr_cycle_step_swapTop]
      refine (catTrace_insertTop_powHom X g k m hkm (g ≫ h)).trans ?_
      rw [Category.assoc, catTrace_comp_comm g (h ≫ (g ^ (k + 1))),
        Category.assoc, pow_comp_self,
        show m + 1 - (k + 1) = m - k from by omega]

/-- **The trace of a cycle against a tensor power**: bubbling the
top factor down `k` slots and letting `g` act on every factor traces
to `tr (g ^ (k + 1))` times one copy of `tr g` for each factor the
bubbling does not reach. -/
theorem catTrace_insertTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [RigidCategory A]
    (X : A) (g : End X) {k n : ℕ}
    (hk : k ≤ n) :
    catTrace (insertTop X n k ≫ powHom X g (n + 1)) =
      catTrace g ^ (n - k) * catTrace (g ^ (k + 1)) := by
  have h := catTrace_insertTop_powHom X g k n hk (𝟙 X)
  rwa [MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Category.id_comp] at h

end RS
