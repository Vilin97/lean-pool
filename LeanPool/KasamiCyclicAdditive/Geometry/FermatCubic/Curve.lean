/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Frobenius

/-!
# The Fermat cubic `X^3 + Y^3 = Z^3` in characteristic two, via a Weierstrass model

Over a field `K` of characteristic two the Fermat cubic `E : X^3+Y^3=Z^3` with origin
`O = [1:1:0]` is isomorphic to the Weierstrass curve

```text
fer :  y^2 + y = x^3 + 1
```

through `x = Z/(X+Y)`, `y = X/(X+Y)`.  Under this isomorphism:

* the affine Fermat points `(w,t)`, `w^3+t^3=1`, correspond to the points with `x ≠ 0`
  (note `w + t ≠ 0` is automatic);
* the three points at infinity `[1:α:0]`, `α^3=1`, correspond to `O` and the two points
  with `x = 0`.

All group-law statements are proved in this model.
-/

namespace KasamiCyclicAdditive.FermatCubic

open WeierstrassCurve

variable {K : Type*} [Field K]

/-- The Weierstrass model `y^2 + y = x^3 + 1` of the Fermat cubic in characteristic two. -/
def fer (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 1, 0, 1⟩

/-! The Weierstrass coefficients of `fer`, as `simp` lemmas. -/

@[simp] lemma fer_a1 : (fer K).a₁ = 0 := rfl
@[simp] lemma fer_a2 : (fer K).a₂ = 0 := rfl
@[simp] lemma fer_a3 : (fer K).a₃ = 1 := rfl
@[simp] lemma fer_a4 : (fer K).a₄ = 0 := rfl
@[simp] lemma fer_a6 : (fer K).a₆ = 1 := rfl

/-- The Weierstrass equation of `fer` in the form `y^2 + y = x^3 + 1`. -/
lemma eq_of_nonsingular {x y : K} (h : (fer K).toAffine.Nonsingular x y) :
    y ^ 2 + y = x ^ 3 + 1 := by
  have h1 := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at h1
  simp only [WeierstrassCurve.toAffine, fer_a1, fer_a2, fer_a3, fer_a4, fer_a6] at h1
  linear_combination h1

/-- Two affine points of `fer` agree once their coordinates do. -/
lemma some_eq_some {x₁ y₁ x₂ y₂ : K} (h₁ : (fer K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (fer K).toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Affine.Point.some _ _ h₁ = Affine.Point.some _ _ h₂ := by
  subst hx; subst hy; rfl

/-- Equal affine points of `fer` have equal coordinates. -/
lemma some_inj {x₁ y₁ x₂ y₂ : K} {h₁ : (fer K).toAffine.Nonsingular x₁ y₁}
    {h₂ : (fer K).toAffine.Nonsingular x₂ y₂}
    (h : Affine.Point.some _ _ h₁ = Affine.Point.some _ _ h₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  rw [Affine.Point.some.injEq] at h
  exact ⟨h.1, h.2⟩

section CharTwo

variable [CharP K 2]

/-- Subtraction is addition in characteristic two. -/
private lemma sub_eq_add' (a b : K) : a - b = a + b := by
  linear_combination -CharTwo.add_self_eq_zero b

/-- Nonsingularity is automatic on `y^2+y = x^3+1` in characteristic two. -/
lemma nonsingular_of_eq {x y : K} (h : y ^ 2 + y = x ^ 3 + 1) :
    (fer K).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine, fer_a1, fer_a2, fer_a3, fer_a4, fer_a6]
    linear_combination h
  · simp only [WeierstrassCurve.toAffine, fer_a1, fer_a3]
    intro hc
    have h2 : (2 : K) * y + 1 = 0 := by linear_combination hc
    rw [CharTwo.two_eq_zero] at h2
    simp at h2

/-- The negation on `fer` is `(x,y) ↦ (x, y+1)`. -/
lemma negY_eq (x y : K) : (fer K).toAffine.negY x y = y + 1 := by
  simp only [WeierstrassCurve.toAffine, Affine.negY, fer_a1, fer_a3]
  linear_combination -CharTwo.add_self_eq_zero y - CharTwo.add_self_eq_zero (1 : K)

/-- Char-two form of `addX`: `l^2 + x₁ + x₂`. -/
lemma addX_eq (x₁ x₂ l : K) : (fer K).toAffine.addX x₁ x₂ l = l ^ 2 + x₁ + x₂ := by
  simp only [WeierstrassCurve.toAffine, Affine.addX, fer_a1, fer_a2]
  linear_combination (-x₁ - x₂) * CharTwo.two_eq_zero (R := K)

/-- Char-two form of `addY`: `l * (addX + x₁) + y₁ + 1`. -/
lemma addY_eq (x₁ x₂ y₁ l : K) :
    (fer K).toAffine.addY x₁ x₂ y₁ l =
      l * ((fer K).toAffine.addX x₁ x₂ l + x₁) + y₁ + 1 := by
  simp only [WeierstrassCurve.toAffine, Affine.addY, Affine.negAddY, negY_eq]
  rw [sub_eq_add' ((fer K).toAffine.addX x₁ x₂ l) x₁]

section Group

variable [DecidableEq K]

omit [DecidableEq K] in
/-- `y` and `negY x y = y + 1` differ, so no affine point of `fer` is `2`-torsion. -/
lemma Y_ne_negY (x y : K) : y ≠ (fer K).toAffine.negY x y := by
  rw [negY_eq]
  intro hc
  have : (1 : K) = 0 := by linear_combination -hc
  exact one_ne_zero this

/-- The tangent slope at `(x,y)` is `x^2`. -/
lemma slope_self (x y : K) : (fer K).toAffine.slope x x y y = x ^ 2 := by
  rw [Affine.slope_of_Y_ne rfl (Y_ne_negY x y), negY_eq]
  simp only [WeierstrassCurve.toAffine, fer_a1, fer_a2, fer_a4]
  rw [show y - (y + 1) = -1 by ring]
  field_simp
  linear_combination (-2 * x ^ 2) * CharTwo.two_eq_zero (R := K)

/-- The secant slope is `(y₁ + y₂) / (x₁ + x₂)`. -/
lemma slope_ne {x₁ x₂ y₁ y₂ : K} (hx : x₁ ≠ x₂) :
    (fer K).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ + y₂) / (x₁ + x₂) := by
  rw [Affine.slope_of_X_ne hx, sub_eq_add' y₁ y₂, sub_eq_add' x₁ x₂]

/-- An affine point of `fer` is `3`-torsion exactly when its `x`-coordinate
satisfies `x^4 = x`. -/
lemma three_torsion_some_iff {x y : K} (h : (fer K).toAffine.Nonsingular x y) :
    (3 : ℕ) • (Affine.Point.some _ _ h) = 0 ↔ x ^ 4 = x := by
  have hdbl : Affine.Point.some _ _ h + Affine.Point.some _ _ h =
      Affine.Point.some _ _ (Affine.nonsingular_add h h fun hxy => (Y_ne_negY x y) hxy.right) :=
    Affine.Point.add_self_of_Y_ne (Y_ne_negY x y)
  have h3 : (3 : ℕ) • (Affine.Point.some _ _ h) = 0 ↔
      Affine.Point.some _ _ h + Affine.Point.some _ _ h = -Affine.Point.some _ _ h := by
    constructor
    · intro hh
      have : Affine.Point.some _ _ h + Affine.Point.some _ _ h + Affine.Point.some _ _ h = 0 := by
        rw [← hh]; abel
      exact eq_neg_of_add_eq_zero_left this
    · intro hh
      have : (3 : ℕ) • (Affine.Point.some _ _ h)
          = Affine.Point.some _ _ h + Affine.Point.some _ _ h + Affine.Point.some _ _ h := by abel
      rw [this, hh]
      exact neg_add_cancel _
  rw [h3, hdbl, Affine.Point.neg_some]
  constructor
  · intro hh
    have hc := some_inj hh
    have hx : (fer K).toAffine.addX x x ((fer K).toAffine.slope x x y y) = x := hc.1
    rw [slope_self, addX_eq] at hx
    linear_combination hx + (-x) * CharTwo.two_eq_zero (R := K)
  · intro hx
    refine some_eq_some _ _ ?_ ?_
    · rw [slope_self, addX_eq]
      linear_combination hx + x * CharTwo.two_eq_zero (R := K)
    · rw [addY_eq, slope_self, addX_eq, negY_eq]
      have h0 : (x ^ 2) ^ 2 + x + x + x = 0 := by
        linear_combination hx + (2 * x) * CharTwo.two_eq_zero (R := K)
      linear_combination (x ^ 2) * h0

end Group

end CharTwo

end KasamiCyclicAdditive.FermatCubic
