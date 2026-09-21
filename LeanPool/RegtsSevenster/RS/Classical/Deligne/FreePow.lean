/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModPowCast
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PlainShuffle
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MuInterchange

/-!
# The relative power of a free module

Over an internal commutative monoid `A` in a symmetric monoidal
category, the module power of the free module `A ⊗ V` collapses to
the free module on the ambient tensor power:
`modPow A (A ⊗ V) (n + 1) ≅ A ⊗ tensorPow D V (n + 1)`.  At arity
zero the module power is the unit object while `A ⊗ 𝟙_ D ≅ A`, so
the collapse starts at arity one.

Throughout, the module structure on `A ⊗ V` is `freeModObj A V` —
multiplication into the head factor — installed as a local instance
for the whole file; the statements of record are spelt at the
carrier `A ⊗ V` with that instance.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The multiplication fold of a monoid power -/

section Fold

/-- **The multiplication fold**: the left-to-right product
`tensorPow D A n ⟶ A`, one factor at a time; the empty product is
the unit. -/
noncomputable def muFold
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    (n : ℕ) → tensorPow D A n ⟶ A
  | 0 => η[A]
  | n + 1 => (muFold A n ▷ A) ≫ μ[A]

@[simp] theorem muFold_zero
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    muFold A 0 = η[A] := rfl

end Fold

/-! ## Permutation invariance of the fold -/

section FoldPerm

/-- The braiding sandwich on the top two factors is natural in the
lower block. -/
private theorem braidTop_natural
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    {P Q : D} (f : P ⟶ Q) :
    ((f ▷ A) ▷ A) ≫ (α_ Q A A).hom ≫ (Q ◁ (β_ A A).hom) ≫
        (α_ Q A A).inv =
      (α_ P A A).hom ≫ (P ◁ (β_ A A).hom) ≫ (α_ P A A).inv ≫
        ((f ▷ A) ▷ A) := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

/-- **Commutativity under a head**: braiding the two top factors is
absorbed by two folds of the multiplication. -/
private theorem braidTop_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A] :
    (α_ A A A).hom ≫ (A ◁ (β_ A A).hom) ≫ (α_ A A A).inv ≫
        (μ[A] ▷ A) ≫ μ[A] = (μ[A] ▷ A) ≫ μ[A] := by
  have h : (α_ A A A).inv ≫ (μ[A] ▷ A) ≫ μ[A] =
      (A ◁ μ[A]) ≫ μ[A] := by
    rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
  rw [h, ← whiskerLeft_comp_assoc, IsCommMonObj.mul_comm,
    ← MonObj.mul_assoc]

/-- The absorption at a generic lower block. -/
private theorem braidTop_mul'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A]
    {P : D} (f : P ⟶ A) :
    (α_ P A A).hom ≫ (P ◁ (β_ A A).hom) ≫ (α_ P A A).inv ≫
        (((f ▷ A) ≫ μ[A]) ▷ A) ≫ μ[A] =
      (((f ▷ A) ≫ μ[A]) ▷ A) ≫ μ[A] := by
  rw [comp_whiskerRight, Category.assoc,
    ← reassoc_of% (braidTop_natural A f), braidTop_mul]

/-- **The top transposition is absorbed by the fold.** -/
theorem swapTop_muFold
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A]
    (n : ℕ) :
    swapTop A n ≫ muFold A (n + 2) = muFold A (n + 2) := by
  have hM : muFold A (n + 2) =
      (((muFold A n ▷ A) ≫ μ[A]) ▷ A) ≫ μ[A] := rfl
  rw [hM]
  unfold swapTop
  repeat' erw [Category.assoc]
  exact braidTop_mul' A (muFold A n)

/-- **Bubbling is absorbed by the fold.** -/
theorem insertTop_muFold
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A] : ∀ n k : ℕ,
    insertTop A n k ≫ muFold A (n + 1) = muFold A (n + 1)
  | _, 0 => by rw [insertTop_zero, Category.id_comp]
  | 0, _ + 1 => by rw [insertTop_of_zero, Category.id_comp]
  | n + 1, k + 1 => by
    have h : (insertTop A n k ▷ A) ≫ muFold A (n + 2) =
        muFold A (n + 2) := by
      show (insertTop A n k ▷ A) ≫ ((muFold A (n + 1) ▷ A) ≫ μ[A])
        = (muFold A (n + 1) ▷ A) ≫ μ[A]
      rw [← Category.assoc, ← comp_whiskerRight,
        insertTop_muFold A n k]
    rw [insertTop_succ]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => swapTop A n ≫ z) h).trans
        (swapTop_muFold A n))

/-- **Permutation invariance of the fold**: the fold of a
commutative monoid absorbs the symmetric-group action. -/
theorem muFold_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permMor A n σ ≫ muFold A n = muFold A n := by
  induction n with
  | zero =>
      show 𝟙 _ ≫ _ = _
      exact Category.id_comp _
  | succ n ih =>
      rw [permMor_succ]
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg
        (fun z => (permMor A n (restPerm σ) ▷ A) ≫ z)
        (insertTop_muFold A n _)).trans ?_
      show (permMor A n (restPerm σ) ▷ A) ≫
          ((muFold A n ▷ A) ≫ μ[A]) = (muFold A n ▷ A) ≫ μ[A]
      rw [← Category.assoc, ← comp_whiskerRight, ih]

end FoldPerm

/-! ## The free collapse -/

section Collect

/-- **The free collapse**: multiply all the heads of a power of
free letters to the front of the word. -/
noncomputable def freeCollapse
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (V : D) : (n : ℕ) →
    tensorPow D (A ⊗ V) n ⟶ A ⊗ tensorPow D V n
  | 0 => (λ_ (𝟙_ D)).inv ≫ (η[A] ▷ 𝟙_ D)
  | n + 1 => (freeCollapse A V n ▷ (A ⊗ V)) ≫
      freeModShuffle A (tensorPow D V n) V

@[simp] theorem freeCollapse_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (V : D) :
    freeCollapse A V 0 = (λ_ (𝟙_ D)).inv ≫ (η[A] ▷ 𝟙_ D) := rfl

/-- The defining recursion of the collapse. -/
theorem freeCollapse_succ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (V : D)
    (n : ℕ) :
    freeCollapse A V (n + 1) =
      (freeCollapse A V n ▷ (A ⊗ V)) ≫
        freeModShuffle A (tensorPow D V n) V := rfl

end Collect

section CollapseShuffle

/-- **The collapse through the diagonal shuffle**: sorting the word
and folding the heads is the collapse. -/
theorem freeCollapse_shuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D)
    (n : ℕ) :
    freeCollapse A V n =
      (plainShuffle A V n).hom ≫
        (muFold A n ▷ tensorPow D V n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : ∀ P : D,
          ((muFold A n ▷ P) ▷ (A ⊗ V)) ≫ freeModShuffle A P V =
            tensorμ (tensorPow D A n) P A V ≫
              (((muFold A n ▷ A) ≫ μ[A]) ▷ (P ⊗ V)) := by
        intro P
        rw [freeModShuffle, ← tensorHom_id (muFold A n) P,
          tensorμ_natural_left_assoc]
        congr 1
        rw [MonoidalCategory.id_whiskerRight,
          ← tensorHom_id μ[A] (P ⊗ V), tensorHom_comp_tensorHom,
          Category.comp_id, tensorHom_id]
      refine Eq.trans (freeCollapse_succ A V n) ?_
      refine Eq.trans (eq_whisker
        (congrArg (fun t => t ▷ (A ⊗ V)) ih) _) ?_
      refine Eq.trans (eq_whisker
        (MonoidalCategory.comp_whiskerRight _ _ _) _) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (whisker_eq _ (hstep (tensorPow D V n))) ?_
      refine Eq.trans ?_ (eq_whisker
        (plainShuffle_succ_hom A V n) _).symm
      exact (Category.assoc _ _ _).symm

/-- **Permutation equivariance of the collapse**: sorting the
free letters and then collapsing is collapsing and then sorting
the ambient letters — the heads are folded by a commutative
multiplication, which absorbs the permutation. -/
theorem freeCollapse_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) [IsCommMonObj A]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permMor (A ⊗ V) n σ ≫ freeCollapse A V n =
      freeCollapse A V n ≫ (A ◁ permMor V n σ) := by
  rw [freeCollapse_shuffle, ← Category.assoc,
    plainShuffle_permMor]
  simp only [Category.assoc]
  refine whisker_eq ((plainShuffle A V n).hom) ?_
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    whisker_exchange, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, muFold_permMor]

end CollapseShuffle

end RS
