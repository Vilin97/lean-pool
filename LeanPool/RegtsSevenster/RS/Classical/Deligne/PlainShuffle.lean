/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixedDiag

/-!
# The plain diagonal shuffle and its equivariance

The diagonal shuffle `(X ⊗ Y) ^ ⊗ n ≅ X ^ ⊗ n ⊗ Y ^ ⊗ n` re-sorts a
tensor power of a tensor product: the empty power is the inverse
unitor, and each step of the recursion is the middle-four
interchange `tensorμ`, inverted by `tensorδ`.  The shuffle is
equivariant for the symmetric-group actions: the diagonal action of
a permutation on the `(X ⊗ Y)`-factors passes through it to the
simultaneous action on the two plain powers.

The isomorphism and its intertwining are carried by the distribution
isomorphism `tensorPowDistrib` of `Deligne/MixedDiag.lean`, whose
top-braiding square reduces to the componentwise braidings through
Mathlib's `tensor_associativity`, and whose functoriality follows
the recursions of `insertTop` and `permMor`.  This module presents
the shuffle under its own name, with the defining recursion
equations on both the forward and the inverse maps and the
equivariance statements in the form the plain tensor-power calculus
consumes.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- **The plain diagonal shuffle**
`(X ⊗ Y) ^ ⊗ n ≅ X ^ ⊗ n ⊗ Y ^ ⊗ n`: the empty power is the inverse
unitor, and each further step of the recursion is the middle-four
interchange `tensorμ`, inverted by `tensorδ`.  It is the
distribution isomorphism `tensorPowDistrib`, under the shuffle's
own name. -/
noncomputable def plainShuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y : D) (n : ℕ) :
    tensorPow D (X ⊗ Y) n ≅ tensorPow D X n ⊗ tensorPow D Y n :=
  tensorPowDistrib X Y n

/-- The empty shuffle is the inverse unitor. -/
@[simp]
theorem plainShuffle_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y : D) :
    plainShuffle X Y 0 = (λ_ (𝟙_ D)).symm := rfl

/-- The defining recursion of the shuffle, on the forward maps: the
lower factors are shuffled and the newest `(X ⊗ Y)`-pair is routed
to its two destinations by the interchange. -/
@[simp]
theorem plainShuffle_succ_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y : D) (n : ℕ) :
    (plainShuffle X Y (n + 1)).hom =
      ((plainShuffle X Y n).hom ▷ (X ⊗ Y)) ≫
        tensorμ (tensorPow D X n) (tensorPow D Y n) X Y := rfl

/-- The defining recursion of the shuffle, on the inverse maps: the
newest pair is split off by the inverse interchange and the lower
factors are unshuffled. -/
@[simp]
theorem plainShuffle_succ_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y : D) (n : ℕ) :
    (plainShuffle X Y (n + 1)).inv =
      tensorδ (tensorPow D X n) (tensorPow D Y n) X Y ≫
        ((plainShuffle X Y n).inv ▷ (X ⊗ Y)) := rfl

/-- **Permutation equivariance of the plain shuffle**: the diagonal
action of a permutation on `(X ⊗ Y) ^ ⊗ n` passes through the
shuffle to its simultaneous action on the two plain tensor
powers. -/
theorem plainShuffle_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y : D) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permMor (X ⊗ Y) n σ ≫ (plainShuffle X Y n).hom =
      (plainShuffle X Y n).hom ≫
        (permMor X n σ ⊗ₘ permMor Y n σ) :=
  tensorPowDistrib_permMor X Y n σ

end RS
