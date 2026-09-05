/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Hessian

/-!
# Explicit quotient coordinates on the Fermat cubic

Given an affine point `(x,y)` of `x³ + y³ = 1` with `x, y ≠ 0` and any cube
root `W` of `w = (x+1)/(x+y)`, the point `(W,T)` with `T = r/W`,
`r = (1+x+y)/(x+y)`, lies on the cubic and has Hessian addition coordinates
exactly `(x,y)`.

This is the algebraic content of "`(x,y)` is the image of `(W,T)` under
`Q ↦ Q + πQ`", proved directly from the defining equation: no group law,
Frobenius endomorphism, or algebraic closure is involved.  Note the direction —
`w` and `z` are produced in `K` first, and `W`, `T` are only cube roots
chosen afterwards.
-/

open KasamiCyclicAdditive.FermatCubic

namespace KasamiCyclicAdditive.FermatCubic

section Aux

variable {K : Type*} [Field K] [CharP K 2] {x y : K}

omit [CharP K 2] in
/-- In characteristic two, `x + y ≠ 0` for a point of the Fermat cubic. -/
private lemma sum_ne_zero (hxy : x ^ 3 + y ^ 3 = 1) : x + y ≠ 0 := by
  intro h
  exact one_ne_zero (α := K)
    (by linear_combination -hxy + (x ^ 2 - x * y + y ^ 2) * h)

/-- The key identity `1 + (x+y)^3 = (x+y) * x * y` in characteristic two. -/
private lemma key_identity (hxy : x ^ 3 + y ^ 3 = 1) :
    1 + (x + y) ^ 3 = (x + y) * x * y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination hxy + (1 + x ^ 2 * y + x * y ^ 2) * h2

/-- In characteristic two, `1 + x + y ≠ 0` for a point of the Fermat cubic
with both coordinates nonzero. -/
private lemma one_add_sum_ne_zero (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ^ 3 + y ^ 3 = 1) :
    1 + x + y ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro h
  have hs : x + y = 1 := by linear_combination -h + (x + y) * h2
  have := key_identity hxy
  rw [hs] at this
  have hxy0 : x * y = 0 := by linear_combination -this + h2
  rcases mul_eq_zero.1 hxy0 with h' | h'
  · exact hx h'
  · exact hy h'

omit [CharP K 2] in
/-- An affine Fermat point with `y ≠ 0` has `x ≠ 1`. -/
private lemma coord_ne_one (hy : y ≠ 0) (hxy : x ^ 3 + y ^ 3 = 1) : x ≠ 1 := by
  intro h
  apply hy
  have : y ^ 3 = 0 := by rw [h] at hxy; linear_combination hxy
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this

end Aux

/-- Evaluation of the Hessian chart at the pair `(W, T)`, `(W², T²)`: given the
lift identities `W * T = r`, `W³ = w` and `T³ = z`, the denominator is nonzero
and the two quotients are `x` and `y`. -/
private lemma hess_quotient_coords {K : Type*} [Field K] [CharP K 2] {x y W T : K}
    (hs : x + y ≠ 0) (hr0 : 1 + x + y ≠ 0)
    (hWT : W * T = (1 + x + y) / (x + y))
    (hW3 : W ^ 3 = (x + 1) / (x + y))
    (hT3 : T ^ 3 = (y + 1) / (x + y)) :
    hessD W T (W ^ 2) (T ^ 2) ≠ 0 ∧
    hessX W T (W ^ 2) (T ^ 2) / hessD W T (W ^ 2) (T ^ 2) = x ∧
    hessY W T (W ^ 2) (T ^ 2) / hessD W T (W ^ 2) (T ^ 2) = y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let w : K := (x + 1) / (x + y)
  let z : K := (y + 1) / (x + y)
  let r : K := (1 + x + y) / (x + y)
  have hwdef : w = (x + 1) / (x + y) := rfl
  have hzdef : z = (y + 1) / (x + y) := rfl
  have hrdef : r = (1 + x + y) / (x + y) := rfl
  have hrne : r ≠ 0 := div_ne_zero hr0 hs
  have hD : hessD W T (W ^ 2) (T ^ 2) = r + r ^ 2 := by
    unfold hessD
    calc W * T + W ^ 2 * T ^ 2 = (W * T) + (W * T) ^ 2 := by ring
      _ = r + r ^ 2 := by rw [hWT]
  have hNx : hessX W T (W ^ 2) (T ^ 2) = r ^ 2 + z * r := by
    unfold hessX
    calc T ^ 2 * W ^ 2 + (T ^ 2) ^ 2 * W = (W * T) ^ 2 + T ^ 3 * (W * T) := by ring
      _ = r ^ 2 + z * r := by rw [hWT, hT3, ← hzdef]
  have hNy : hessY W T (W ^ 2) (T ^ 2) = r ^ 2 + w * r := by
    unfold hessY
    calc W ^ 2 * T ^ 2 + (W ^ 2) ^ 2 * T = (W * T) ^ 2 + W ^ 3 * (W * T) := by ring
      _ = r ^ 2 + w * r := by rw [hWT, hW3, ← hwdef]
  have h1r : 1 + r = 1 / (x + y) := by
    rw [hrdef]; field_simp; linear_combination (x + y) * h2
  have h1rne : 1 + r ≠ 0 := by rw [h1r]; exact one_div_ne_zero hs
  have hDne : hessD W T (W ^ 2) (T ^ 2) ≠ 0 := by
    rw [hD]
    have : r + r ^ 2 = r * (1 + r) := by ring
    rw [this]
    exact mul_ne_zero hrne h1rne
  have hrz : r + z = x / (x + y) := by
    rw [hrdef, hzdef]; field_simp; linear_combination (1 + y) * h2
  have hrw : r + w = y / (x + y) := by
    rw [hrdef, hwdef]; field_simp; linear_combination (1 + x) * h2
  refine ⟨hDne, ?_, ?_⟩
  · rw [hNx, hD]
    have : r ^ 2 + z * r = r * (r + z) := by ring
    rw [this, show r + r ^ 2 = r * (1 + r) by ring,
      mul_div_mul_left _ _ hrne, hrz, h1r]
    field_simp
  · rw [hNy, hD]
    have : r ^ 2 + w * r = r * (r + w) := by ring
    rw [this, show r + r ^ 2 = r * (1 + r) by ring,
      mul_div_mul_left _ _ hrne, hrw, h1r]
    field_simp

/-- The explicit degree-three quotient lift of `(x, y)` through a chosen cube
root `W` of `(x + 1) / (x + y)`. -/
def quotientT {K : Type*} [Field K] (x y W : K) : K := (1 + x + y) / (x + y) / W

/--
Explicit quotient-coordinate lemma.

Let `K` have characteristic two and let `(x,y)` be a non-3-torsion
affine point of the Fermat cubic

    x^3 + y^3 = 1

with `x,y ≠ 0`.

Suppose `W` is any cube root of `w = (x+1)/(x+y)`, and let `T = quotientT x y W`
be the lift `((1+x+y)/(x+y))/W`.  Then

* `T^3 = (y+1)/(x+y)`,
* hence `W^3+T^3=1`,
* the Hessian denominator for `(W,T)` and `(W^2,T^2)` is nonzero,
* and the Hessian addition coordinates are exactly `(x,y)`:

    hessX(W,T,W²,T²) / hessD(W,T,W²,T²) = x,
    hessY(W,T,W²,T²) / hessD(W,T,W²,T²) = y.

This is the explicit algebraic statement that `(x,y)` is the image of
`(W,T)` under the quotient map represented by `Q ↦ Q + Frobenius(Q)`,
established from the formulas above alone, with no elliptic-curve group law.
-/
theorem explicit_quotient_coordinates
    {K : Type*}
    [Field K] [CharP K 2]
    {x y W : K}
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hxy : x ^ 3 + y ^ 3 = 1)
    (hW :
      W ^ 3 = (x + 1) / (x + y)) :
    let T : K := quotientT x y W
    T ^ 3 = (y + 1) / (x + y) ∧
    W ^ 3 + T ^ 3 = 1 ∧
    hessD W T (W ^ 2) (T ^ 2) ≠ 0 ∧
    hessX W T (W ^ 2) (T ^ 2) /
        hessD W T (W ^ 2) (T ^ 2) = x ∧
    hessY W T (W ^ 2) (T ^ 2) /
        hessD W T (W ^ 2) (T ^ 2) = y := by
  intro T
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  -- the auxiliary quantities of the construction; `w + z = 1` and `r ^ 3 = w * z`
  -- are internal to the algebra below, not part of the quotient interface
  let w : K := (x + 1) / (x + y)
  let z : K := (y + 1) / (x + y)
  let r : K := (1 + x + y) / (x + y)
  have hwdef : w = (x + 1) / (x + y) := rfl
  have hzdef : z = (y + 1) / (x + y) := rfl
  have hrdef : r = (1 + x + y) / (x + y) := rfl
  have hs : x + y ≠ 0 := sum_ne_zero hxy
  have hx1 : x ≠ 1 := coord_ne_one hy hxy
  have hxa : x + 1 ≠ 0 := fun h => hx1 (by linear_combination h - h2)
  have hr0 : 1 + x + y ≠ 0 := one_add_sum_ne_zero hx hy hxy
  have hTdef : T = r / W := rfl
  have hwne : w ≠ 0 := div_ne_zero hxa hs
  have hWne : W ≠ 0 := by
    intro h
    rw [h] at hW
    exact hwne (by rw [hwdef, ← hW]; ring)
  -- basic identities
  have hwz : w + z = 1 := by
    rw [hwdef, hzdef]
    field_simp
    linear_combination h2
  have hr3 : r ^ 3 = w * z := by
    rw [hwdef, hzdef, hrdef]
    have hkey := key_identity (x := x) (y := y) hxy
    field_simp
    linear_combination hkey + ((x + y) + (x + y) ^ 2) * h2
  have hWT : W * T = r := by
    rw [hTdef]; field_simp
  have hT3 : T ^ 3 = z := by
    have : T ^ 3 * W ^ 3 = z * W ^ 3 := by
      calc T ^ 3 * W ^ 3 = (W * T) ^ 3 := by ring
        _ = r ^ 3 := by rw [hWT]
        _ = w * z := hr3
        _ = z * W ^ 3 := by rw [hW, ← hwdef]; ring
    exact mul_right_cancel₀ (pow_ne_zero 3 hWne) this
  have hsum : W ^ 3 + T ^ 3 = 1 := by
    rw [hT3, hW, ← hwdef]; exact hwz
  -- the Hessian chart is then evaluated from these lift identities
  obtain ⟨hDne, hXeq, hYeq⟩ := hess_quotient_coords hs hr0 hWT hW hT3
  exact ⟨hT3, hsum, hDne, hXeq, hYeq⟩



end KasamiCyclicAdditive.FermatCubic
