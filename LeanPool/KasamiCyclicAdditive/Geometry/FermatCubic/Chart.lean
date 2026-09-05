/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Hessian

/-!
# The affine Fermat chart and the Hessian addition formula

`pt w t h` is the affine Fermat point `(w,t)` (`w^3+t^3=1`) seen inside the Weierstrass
model `fer`.  The main results are

* `add_pt`: if the Hessian denominator `D0` is nonzero, then
  `(w1,t1) + (w2,t2) = (N_x/D0, N_y/D0)`, which is the affine Hessian addition formula
  used for the chart;
* `neg_pt`: negation swaps the two affine coordinates;
* `three_torsion_pt_iff`: an affine Fermat point is `3`-torsion iff one of its coordinates
  vanishes.
-/

namespace KasamiCyclicAdditive.FermatCubic

open WeierstrassCurve

variable {K : Type*} [Field K] [CharP K 2]

/-- An affine Fermat point has `w + t ≠ 0`. -/
lemma den_ne_zero {w t : K} (h : w ^ 3 + t ^ 3 = 1) : w + t ≠ 0 := by
  intro h0
  have ht : t = w := by linear_combination h0 - CharTwo.add_self_eq_zero w
  rw [ht, CharTwo.add_self_eq_zero (w ^ 3)] at h
  exact zero_ne_one h

/-- `w*t*(w+t) = 1 + (w+t)^3` on the Fermat cubic. -/
private lemma prod_den {w t : K} (h : w ^ 3 + t ^ 3 = 1) : w * t * (w + t) = 1 + (w + t) ^ 3 := by
  linear_combination -h + (-(w ^ 2 * t) - w * t ^ 2 - 1) * CharTwo.two_eq_zero (R := K)

/-- The chart coordinates `((w+t)⁻¹, w * (w+t)⁻¹)` of an affine Fermat point are
nonsingular on `fer K`. -/
lemma chart_nonsingular {w t : K} (h : w ^ 3 + t ^ 3 = 1) :
    (fer K).toAffine.Nonsingular ((w + t)⁻¹) (w * (w + t)⁻¹) := by
  refine nonsingular_of_eq ?_
  have hd := den_ne_zero h
  field_simp
  linear_combination h + (-t ^ 3 - w * t ^ 2) * CharTwo.two_eq_zero (R := K)

/-- The affine Fermat point `(w,t)` viewed in the Weierstrass model `fer`. -/
def pt (w t : K) (h : w ^ 3 + t ^ 3 = 1) : (fer K).toAffine.Point :=
  Affine.Point.some _ _ (chart_nonsingular h)

/-- `pt` is injective in its two coordinates. -/
lemma pt_inj {w t w' t' : K} {h : w ^ 3 + t ^ 3 = 1} {h' : w' ^ 3 + t' ^ 3 = 1}
    (he : pt w t h = pt w' t' h') : w = w' ∧ t = t' := by
  obtain ⟨hx, hy⟩ := some_inj he
  have hd := den_ne_zero h
  have hd' := den_ne_zero h'
  have hdd : w + t = w' + t' := by
    have := congrArg (fun z : K => z⁻¹) hx
    simpa [hd, hd'] using this
  have hw : w = w' := by
    rw [hdd] at hy
    field_simp at hy
    exact hy
  refine ⟨hw, ?_⟩
  have ht : t + t' = 0 := by linear_combination hdd - hw + t' * CharTwo.two_eq_zero (R := K)
  linear_combination ht + (-t') * CharTwo.two_eq_zero (R := K)

omit [CharP K 2] in
/-- The Fermat equation is symmetric in its two coordinates. -/
private lemma fermat_symm {w t : K} (h : w ^ 3 + t ^ 3 = 1) : t ^ 3 + w ^ 3 = 1 := by
  linear_combination h

/-- Negation on the Fermat cubic swaps the two affine coordinates. -/
theorem neg_pt {w t : K} (h : w ^ 3 + t ^ 3 = 1) : -(pt w t h) = pt t w (fermat_symm h) := by
  rw [pt, pt, Affine.Point.neg_some]
  refine some_eq_some _ _ ?_ ?_
  · rw [show t + w = w + t by ring]
  · rw [negY_eq, show t + w = w + t by ring]
    have hd := den_ne_zero h
    field_simp
    linear_combination w * CharTwo.two_eq_zero (R := K)


section Group

variable [DecidableEq K]
variable {w1 t1 w2 t2 : K}

omit [DecidableEq K] in
/-- If two affine Fermat points have the same `x`-coordinate in the Weierstrass model,
then the Hessian denominator vanishes. -/
lemma hessD_eq_zero_of_den_eq (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hdd : w1 + t1 = w2 + t2) : hessD w1 t1 w2 t2 = 0 := by
  have hd1 := den_ne_zero h1
  have hp1 := prod_den h1
  have hp2 := prod_den h2
  rw [← hdd] at hp2
  have : (w1 * t1) * (w1 + t1) = (w2 * t2) * (w1 + t1) := by rw [hp1, hp2]
  have hmul : w1 * t1 = w2 * t2 := by
    exact mul_right_cancel₀ hd1 this
  rw [hessD, hmul]
  exact CharTwo.add_self_eq_zero _

omit [DecidableEq K] in
/-- A nonzero Hessian denominator forces the two Hessian numerators to differ. -/
lemma hessS_ne_zero (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hD : hessD w1 t1 w2 t2 ≠ 0) : hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2 ≠ 0 := by
  intro hS
  apply hD
  have hXY : hessY w1 t1 w2 t2 = hessX w1 t1 w2 t2 := by
    linear_combination hS - CharTwo.add_self_eq_zero (hessX w1 t1 w2 t2)
  have hc := hess_cubic h1 h2
  rw [hXY, CharTwo.add_self_eq_zero] at hc
  have : hessD w1 t1 w2 t2 ^ 3 = 0 := hc.symm
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this

omit [DecidableEq K] in
/-- The Hessian sum of two affine Fermat points is again an affine Fermat point,
provided the denominator is nonzero. -/
lemma hess_fermat (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hD : hessD w1 t1 w2 t2 ≠ 0) :
    (hessX w1 t1 w2 t2 / hessD w1 t1 w2 t2) ^ 3 + (hessY w1 t1 w2 t2 / hessD w1 t1 w2 t2) ^ 3
      = 1 := by
  have hc := hess_cubic h1 h2
  field_simp
  linear_combination hc

omit [DecidableEq K] in
/-- If the two points have distinct `w+t`, then `(w1+t1)+(w2+t2) ≠ 0`. -/
lemma sum_den_ne_zero (hdd : w1 + t1 ≠ w2 + t2) : (w1 + t1) + (w2 + t2) ≠ 0 := by
  intro hc
  exact hdd (by linear_combination hc - CharTwo.add_self_eq_zero (w2 + t2))

omit [CharP K 2] [DecidableEq K] in
/-- Distinct `w+t` give distinct Weierstrass `x`-coordinates. -/
lemma x_ne_of_den_ne (hdd : w1 + t1 ≠ w2 + t2) : ((w1 + t1)⁻¹ : K) ≠ (w2 + t2)⁻¹ :=
  fun hc => hdd (inv_injective hc)

/-- The secant slope through two affine Fermat points with distinct `w+t`. -/
lemma secant_slope (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hdd : w1 + t1 ≠ w2 + t2) :
    (fer K).toAffine.slope ((w1 + t1)⁻¹) ((w2 + t2)⁻¹) (w1 * (w1 + t1)⁻¹) (w2 * (w2 + t2)⁻¹)
      = (w1 * (w2 + t2) + w2 * (w1 + t1)) / ((w1 + t1) + (w2 + t2)) := by
  have hd1 := den_ne_zero h1
  have hd2 := den_ne_zero h2
  have hg := sum_den_ne_zero hdd
  have hinv : (w1 + t1)⁻¹ + (w2 + t2)⁻¹ ≠ 0 := by
    intro hc
    apply hg
    field_simp at hc
    linear_combination hc
  rw [slope_ne (x_ne_of_den_ne hdd), div_eq_div_iff hinv hg]
  field_simp
  ring

/-- The `x`-coordinate of the sum of two affine Fermat points with distinct `w+t`. -/
lemma addX_secant (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hdd : w1 + t1 ≠ w2 + t2) :
    (fer K).toAffine.addX ((w1 + t1)⁻¹) ((w2 + t2)⁻¹)
      ((fer K).toAffine.slope ((w1 + t1)⁻¹) ((w2 + t2)⁻¹) (w1 * (w1 + t1)⁻¹)
        (w2 * (w2 + t2)⁻¹))
      = ((w1 * (w2 + t2) + w2 * (w1 + t1)) ^ 2 * ((w1 + t1) * (w2 + t2))
          + ((w1 + t1) + (w2 + t2)) ^ 3)
        / (((w1 + t1) + (w2 + t2)) ^ 2 * ((w1 + t1) * (w2 + t2))) := by
  have hd1 := den_ne_zero h1
  have hd2 := den_ne_zero h2
  have hg := sum_den_ne_zero hdd
  rw [addX_eq, secant_slope h1 h2 hdd]
  field_simp
  ring

/-- **The affine Hessian addition formula.**  If the denominator `D0 = w1*t1 + w2*t2` is
nonzero, the sum of the two affine Fermat points is the affine Fermat point
`(N_x/D0, N_y/D0)`. -/
theorem add_pt (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hD : hessD w1 t1 w2 t2 ≠ 0) :
    pt w1 t1 h1 + pt w2 t2 h2 =
      pt (hessX w1 t1 w2 t2 / hessD w1 t1 w2 t2) (hessY w1 t1 w2 t2 / hessD w1 t1 w2 t2)
        (hess_fermat h1 h2 hD) := by
  have hd1 := den_ne_zero h1
  have hd2 := den_ne_zero h2
  have hS := hessS_ne_zero h1 h2 hD
  have hdd : w1 + t1 ≠ w2 + t2 := fun hc => hD (hessD_eq_zero_of_den_eq h1 h2 hc)
  have hg := sum_den_ne_zero hdd
  have hx := x_ne_of_den_ne (K := K) hdd
  have hsl := secant_slope h1 h2 hdd
  -- the `x`-coordinate of the sum
  have hX3 : (fer K).toAffine.addX ((w1 + t1)⁻¹) ((w2 + t2)⁻¹)
      ((fer K).toAffine.slope ((w1 + t1)⁻¹) ((w2 + t2)⁻¹) (w1 * (w1 + t1)⁻¹)
        (w2 * (w2 + t2)⁻¹))
      = hessD w1 t1 w2 t2 / (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2) := by
    rw [addX_secant h1 h2 hdd,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hg) (mul_ne_zero hd1 hd2)) hS]
    exact hess_addX_aux h1 h2
  rw [pt, pt, Affine.Point.add_of_X_ne hx, pt]
  refine some_eq_some _ _ ?_ ?_
  · rw [hX3, ← add_div, inv_div]
  · rw [addY_eq, hX3, hsl, ← add_div, inv_div]
    have hlhs : (w1 * (w2 + t2) + w2 * (w1 + t1)) / ((w1 + t1) + (w2 + t2))
          * (hessD w1 t1 w2 t2 / (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2) + (w1 + t1)⁻¹)
          + w1 * (w1 + t1)⁻¹ + 1
        = ((w1 * (w2 + t2) + w2 * (w1 + t1))
              * (hessD w1 t1 w2 t2 * (w1 + t1) + (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2))
            + w1 * ((w1 + t1) + (w2 + t2)) * (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2)
            + ((w1 + t1) + (w2 + t2)) * (w1 + t1) * (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2))
          / (((w1 + t1) + (w2 + t2)) * (w1 + t1) * (hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2)) := by
      field_simp
    rw [hlhs, hess_addY_aux h1 h2]
    field_simp

/-- If the Hessian denominator vanishes while the two Hessian numerators differ,
and the two points have distinct `w+t`, then the sum is a point at infinity: its
`x`-coordinate is `0`. -/
theorem add_pt_x_eq_zero (h1 : w1 ^ 3 + t1 ^ 3 = 1) (h2 : w2 ^ 3 + t2 ^ 3 = 1)
    (hdd : w1 + t1 ≠ w2 + t2) (hD : hessD w1 t1 w2 t2 = 0)
    (hS : hessX w1 t1 w2 t2 + hessY w1 t1 w2 t2 ≠ 0) :
    (fer K).toAffine.addX ((w1 + t1)⁻¹) ((w2 + t2)⁻¹)
      ((fer K).toAffine.slope ((w1 + t1)⁻¹) ((w2 + t2)⁻¹) (w1 * (w1 + t1)⁻¹)
        (w2 * (w2 + t2)⁻¹)) = 0 := by
  have hnum : (w1 * (w2 + t2) + w2 * (w1 + t1)) ^ 2 * ((w1 + t1) * (w2 + t2))
      + ((w1 + t1) + (w2 + t2)) ^ 3 = 0 := by
    have hA := hess_addX_aux h1 h2
    rw [hD, zero_mul] at hA
    exact (mul_eq_zero.mp hA).resolve_right hS
  rw [addX_secant h1 h2 hdd, hnum, zero_div]

/-- An affine Fermat point is `3`-torsion if and only if one of its two
affine coordinates vanishes.  (The remaining three points of `E[3]` are the points at
infinity.) -/
theorem three_torsion_pt_iff {w t : K} (h : w ^ 3 + t ^ 3 = 1) :
    (3 : ℕ) • pt w t h = 0 ↔ w = 0 ∨ t = 0 := by
  have hd := den_ne_zero h
  have hp := prod_den h
  rw [pt, three_torsion_some_iff]
  constructor
  · intro hx4
    have hcube : (w + t) ^ 3 = 1 := by
      field_simp at hx4
      linear_combination -hx4
    rw [hcube] at hp
    have h0 : w * t * (w + t) = 0 := by
      rw [hp]
      linear_combination CharTwo.two_eq_zero (R := K)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact mul_eq_zero.mp h1
    · exact absurd h1 hd
  · intro hwt
    have h0 : w * t = 0 := by
      rcases hwt with h1 | h1 <;> rw [h1] <;> ring
    rw [h0, zero_mul] at hp
    have hcube : (w + t) ^ 3 = 1 := by linear_combination -hp - CharTwo.two_eq_zero (R := K)
    field_simp
    linear_combination -hcube

end Group

end KasamiCyclicAdditive.FermatCubic
