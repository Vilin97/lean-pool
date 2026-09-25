/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaAlgebra

/-!
# Multiplication by a scalar

For an algebra `R` in a monoidal category, an element `g : 𝟙 ⟶ R`
of the even part of its Γ-algebra acts on `R` by multiplication.
The resulting endomorphism `RS.mulBy g` sends the unit to `g`, and
composing any element of the Γ-algebra into it is the convolution
product with `g`.

This is the calculus behind the scalar computation for a simple
algebra: multiplication by a nonzero even element has an ideal for
its kernel and an ideal for its image, so simplicity makes it
invertible, and the preimage of the unit is then an inverse for `g`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section Basic

variable {D : Type u}

/-- **Multiplication by an even scalar.** -/
noncomputable def mulBy [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    (g : 𝟙_ D ⟶ R) : R ⟶ R :=
  (λ_ R).inv ≫ gmul g (𝟙 R)

/-- Multiplication by a scalar, applied to any element of the
Γ-algebra, is the convolution product. -/
theorem comp_mulBy [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {X : D} (g : 𝟙_ D ⟶ R) (h : X ⟶ R) :
    h ≫ mulBy R g = (λ_ X).inv ≫ gmul g h := by
  rw [mulBy, ← Category.assoc, MonoidalCategory.leftUnitor_inv_naturality,
    Category.assoc, ← gmul_comp, Category.comp_id]

/-- Multiplication by a scalar sends the unit to that scalar. -/
@[simp]
theorem unit_comp_mulBy [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    (g : 𝟙_ D ⟶ R) : η[R] ≫ mulBy R g = g := by
  rw [comp_mulBy, gmul_one_right, ← MonoidalCategory.unitors_equal,
    Iso.inv_hom_id_assoc]

/-- Multiplication by the unit is the identity. -/
@[simp]
theorem mulBy_one [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R] :
    mulBy R η[R] = 𝟙 R := by
  rw [mulBy, gmul_one_left, Iso.inv_hom_id_assoc]

end Basic

section Additive

variable {D : Type u}

/-- Multiplication by a scalar is additive in the scalar. -/
theorem mulBy_add [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R]
    (g g' : 𝟙_ D ⟶ R) :
    mulBy R (g + g') = mulBy R g + mulBy R g' := by
  rw [mulBy, mulBy, mulBy, add_gmul, Preadditive.comp_add]

/-- Multiplication by the zero scalar is zero. -/
@[simp]
theorem mulBy_zero [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R] :
    mulBy R (0 : 𝟙_ D ⟶ R) = 0 := by
  have h : mulBy R 0 + mulBy R 0 = mulBy R 0 + 0 := by
    rw [← mulBy_add, add_zero, add_zero]
  exact add_left_cancel h

/-- A scalar whose multiplication vanishes is itself zero. -/
theorem eq_zero_of_mulBy_eq_zero
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] (R : D) [MonObj R]
    {g : 𝟙_ D ⟶ R}
    (h : mulBy R g = 0) : g = 0 := by
  have hg := unit_comp_mulBy R g
  rw [h, Limits.comp_zero] at hg
  exact hg.symm

end Additive

section Odd

variable {D : Type u}

/-- **An odd scalar squares to zero.**  The self-braiding of the odd
line is `−1`, and convolution against a commutative algebra is
commutative up to that braiding, so the square of an odd element is
its own negative. -/
theorem gmul_self_eq_zero_of_oddLine
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] (R : D) [MonObj R] [IsCommMonObj R]
    (L : OddLine D) (f : L.obj ⟶ R) :
    gmul f f = 0 := by
  have hc : gmul f f = (β_ L.obj L.obj).hom ≫ gmul f f := gmul_comm f f
  rw [L.braid_neg, Preadditive.neg_comp, Category.id_comp] at hc
  have h2 : gmul f f + gmul f f = 0 := by
    rw [← neg_eq_iff_add_eq_zero]
    exact hc.symm
  have h3 : (2 : ℂ) • gmul f f = 0 := by
    rw [two_smul]
    exact h2
  have h4 := congrArg (fun t => ((2 : ℂ)⁻¹) • t) h3
  simpa [smul_smul] using h4

end Odd

end RS
