/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPermCast

/-!
# Schur-functor vanishing at the idempotent level

Deligne's Schur functor `S_μ(X)` (Catégories tensorielles, 1.4) is
the multiplicity space of the shape `μ` in the tensor power
`X ^ ⊗ μ.card`; its vanishing is equivalent to the vanishing of the
`μ`-isotypic summand, which is the image of the central idempotent
`e μ` acting through `permAlg`.  This module phrases the condition
on the idempotent's action — no image objects are needed — and
proves Deligne's upward closure (Catégories tensorielles, 1.7) from
the Schur package alone: `branching` puts a nonzero sandwich
`e μ · (e λ ⊗ 1) · e μ` in the block of `μ`, `block_faithful`
turns nonvanishing of `e μ`'s action into injectivity on that
block, and `permAlg_compat` carries the vanishing of `e λ`'s
action up the standard embedding.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-- **Schur vanishing**: the shape `μ` kills `X` when the central
idempotent of its block acts as zero on the `μ.card`-th tensor
power of `X`.  This is the vanishing of the `μ`-isotypic summand
of `X ^ ⊗ μ.card`, i.e. of Deligne's Schur functor `S_μ(X)`. -/
def SchurKilled [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (P : SchurPackage.{v}) (X : A) (μ : YoungDiagram) :
    Prop :=
  permAlg X μ.card (P.e μ) = 0

/-- **Upward closure of Schur vanishing** (Catégories
tensorielles, 1.7): if the shape `λ` kills `X` then so does every
shape containing it. -/
theorem SchurKilled.mono
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (P : SchurPackage.{v}) {X : A}
    {lam mu : YoungDiagram} (hle : lam ≤ mu)
    (h : SchurKilled P X lam) : SchurKilled P X mu := by
  by_contra hne
  have hcard : lam.card ≤ mu.card := YoungDiagram.card_le_card hle
  have hlow : permAlg X mu.card (symCast hcard (P.e lam)) = 0 :=
    permAlg_compat X hcard _ h
  have hz : permAlg X mu.card
      (P.e mu * (symCast hcard (P.e lam) * P.e mu)) = 0 := by
    rw [map_mul, map_mul, hlow, zero_mul, mul_zero]
  have hker := P.block_faithful mu _ (permAlg X mu.card) hne _ hz
  rw [← mul_assoc] at hker
  exact P.branching lam mu hle hcard hker
end RS
