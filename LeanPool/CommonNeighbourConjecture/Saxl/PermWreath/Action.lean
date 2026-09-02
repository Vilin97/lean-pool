/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Defs

/-!
# The product action of a permutation wreath product

For `g = (f, q)` the action on `ι → Δ` is

`(g • x) i = f i • x (q⁻¹ • i)`.
-/

namespace Saxl

variable (X Q ι Δ : Type*)
variable [Group X] [Group Q] [MulAction Q ι] [MulAction X Δ]

/-- The product action of an arbitrary permutation wreath product. -/
instance permWreathMulAction : MulAction (PermWreath X Q ι) (ι → Δ) where
  smul g x i := g.left i • x (g.right⁻¹ • i)
  one_smul x := by
    funext i
    change (1 : X) • x ((1 : Q)⁻¹ • i) = x i
    simp only [inv_one, one_smul]
  mul_smul g h x := by
    funext i
    change
      (g.left i * h.left (g.right⁻¹ • i)) •
          x ((g.right * h.right)⁻¹ • i) =
        g.left i • (h.left (g.right⁻¹ • i) •
          x (h.right⁻¹ • (g.right⁻¹ • i)))
    simp only [mul_inv_rev, mul_smul]

/-- The defining coordinate formula for the product action. -/
@[simp]
theorem permWreath_smul_apply (g : PermWreath X Q ι) (x : ι → Δ) (i : ι) :
    (g • x) i = g.left i • x (g.right⁻¹ • i) := rfl

/-- Coordinate form of the identity law. -/
theorem one_smul_coord (x : ι → Δ) (i : ι) :
    ((1 : PermWreath X Q ι) • x) i = x i := by
  simp

/-- Fully expanded coordinate form of the multiplication law. -/
theorem mul_smul_coord (g h : PermWreath X Q ι) (x : ι → Δ) (i : ι) :
    ((g * h) • x) i =
      g.left i • (h.left (g.right⁻¹ • i) •
        x (h.right⁻¹ • (g.right⁻¹ • i))) := by
  simp [mul_smul]

/-- A base-group element acts independently in each coordinate. -/
theorem base_smul_coord (f : ι → X) (x : ι → Δ) (i : ι) :
    (PermWreath.base X Q ι f • x) i = f i • x i := by
  simp

/-- A top-group element acts by reindexing the coordinates. -/
theorem top_smul_coord (q : Q) (x : ι → Δ) (i : ι) :
    (PermWreath.top X Q ι q • x) i = x (q⁻¹ • i) := by
  simp

end Saxl
