/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.WhiskerAdditive
import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemmaData
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurVanishing

/-!
# The trichotomy statement

Deligne's Proposition 2.9, the consumed direction: an object
killed by some Schur functor is locally a sum of copies of the
unit and an odd line.  The odd line is an object squaring to the
unit with braiding `−1`; local means after base change to some
nonzero commutative algebra.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable (D : Type u)

/-- **An odd line**: an object squaring to the unit whose
self-braiding is `−1`. -/
structure OddLine
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    where
  /-- The underlying object. -/
  obj : D
  /-- The square of the line is the unit. -/
  sq : obj ⊗ obj ≅ 𝟙_ D
  /-- The self-braiding of the line is `−1`. -/
  braid_neg : (β_ obj obj).hom = -𝟙 (obj ⊗ obj)

variable {D}

/-- The mixed sum of `p` copies of the unit and `q` copies of the
line. -/
noncomputable def OddLine.mix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (p q : ℕ) : D :=
  ⨁ fun i : Fin p ⊕ Fin q =>
    Sum.elim (fun _ => 𝟙_ D) (fun _ => L.obj) i

/-- The empty mixed sum is the zero object. -/
theorem OddLine.isZero_mix_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) :
    Limits.IsZero (L.mix 0 0) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact absurd h (Nat.not_lt_zero _)

/-- **Locally mixed**: after base change to some nonzero
commutative algebra, the object becomes a sum of copies of the
unit and the line. -/
def OddLine.LocallyMixed
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (X : D) : Prop :=
  ∃ (p q : ℕ) (A : D) (_ : MonObj A) (_ : IsCommMonObj A),
    η[A] ≠ 0 ∧
    Nonempty (freeMod A X ≅ freeMod A (L.mix p q))

/-- **Tensoring with the odd line reflects vanishing**: the
square of the line collapses to the unit, so the double twist is
the identity up to isomorphism. -/
theorem OddLine.isZero_tensor_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D]
    (L : OddLine D) (Y : D) :
    Limits.IsZero (L.obj ⊗ Y) ↔ Limits.IsZero Y := by
  constructor
  · intro h
    have h2 : Limits.IsZero (L.obj ⊗ (L.obj ⊗ Y)) :=
      isZero_whiskerLeft _ h
    refine Limits.IsZero.of_iso h2 ?_
    exact (λ_ Y).symm ≪≫
      (whiskerRightIso L.sq.symm Y) ≪≫ α_ L.obj L.obj Y
  · exact isZero_whiskerLeft _

/-- **The trichotomy statement of record** (Deligne 2.9, the
consumed direction): an object killed by some Schur functor is
locally a mixed sum of the unit and the odd line. -/
def Prop29Statement [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [CategoryTheory.Linear ℂ D]
    (P : SchurPackage.{v}) (L : OddLine D)
    (X : D) : Prop :=
  (∃ lam : YoungDiagram, SchurKilled P X lam) →
    L.LocallyMixed X

end RS
