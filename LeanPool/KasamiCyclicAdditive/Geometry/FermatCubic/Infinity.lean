/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Chart

/-!
# The points at infinity of the Fermat cubic and the diagonal translation formula

The three points at infinity `P_a = [1:a:0]`, `a^3 = 1`, of the Fermat cubic correspond in the
Weierstrass model `fer` to the origin (`a = 1`) and to the two affine points `(0,a)` with
`a^2+a+1 = 0`.  They form the set `K0`: `neg_ptInf` shows
`-P_a = P_{a^2} = pi(P_a)`, i.e. `(1+pi) P_a = O`, and `three_torsion_ptInf` shows
`K0 ⊆ E[3]`.

The main result is the diagonal translation formula:

```text
(w,t) + P_a = (a*w, a^{-1}*t)          (a^{-1} = a^2).
```
-/

namespace KasamiCyclicAdditive.FermatCubic

open WeierstrassCurve

variable {K : Type*} [Field K] [CharP K 2]

/-- A cube root of unity other than `1` satisfies `a^2 + a + 1 = 0`. -/
lemma cube_root_rel {a : K} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) : a ^ 2 + a + 1 = 0 := by
  have hfac : (a + 1) * (a ^ 2 + a + 1) = 0 := by
    linear_combination ha + (a ^ 2 + a + 1) * CharTwo.two_eq_zero (R := K)
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h - CharTwo.two_eq_zero (R := K) : a = 1) ha1
  · exact h

/-- Conversely, `a^2 + a + 1 = 0` makes `a` a cube root of unity. -/
lemma cube_root_of_rel {a : K} (ha2 : a ^ 2 + a + 1 = 0) : a ^ 3 = 1 := by
  linear_combination (a + 1) * ha2 - (a ^ 2 + a + 1) * CharTwo.two_eq_zero (R := K)

/-- `(0, a)` with `a^2 + a + 1 = 0` is a nonsingular point of `fer K`. -/
lemma inf_nonsingular {a : K} (ha2 : a ^ 2 + a + 1 = 0) :
    (fer K).toAffine.Nonsingular (0 : K) a :=
  nonsingular_of_eq (by linear_combination ha2 - CharTwo.two_eq_zero (R := K))

variable [DecidableEq K]

/-- The point at infinity `P_a = [1:a:0]` of the Fermat cubic, `a^3 = 1`, in the Weierstrass
model.  For `a = 1` this is the origin `O = [1:1:0]`. -/
def ptInf (a : K) (ha : a ^ 3 = 1) : (fer K).toAffine.Point :=
  if ha1 : a = 1 then 0 else Affine.Point.some _ _ (inf_nonsingular (cube_root_rel ha ha1))

/-- `P_1` is the origin. -/
@[simp] lemma ptInf_one : ptInf (1 : K) (one_pow 3) = 0 := by
  simp [ptInf]

/-- For `a ≠ 1` the point at infinity `P_a` is the affine point `(0, a)`. -/
lemma ptInf_ne_one {a : K} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ptInf a ha = Affine.Point.some _ _ (inf_nonsingular (cube_root_rel ha ha1)) := by
  simp [ptInf, ha1]

/-- Every point at infinity is `3`-torsion: `K0 ⊆ E[3]`. -/
theorem three_torsion_ptInf {a : K} (ha : a ^ 3 = 1) : (3 : ℕ) • ptInf a ha = 0 := by
  by_cases ha1 : a = 1
  · subst ha1; simp
  · rw [ptInf_ne_one ha ha1, three_torsion_some_iff]
    ring


omit [CharP K 2] [DecidableEq K] in
/-- The two coordinates of `(a*w, a^2*t)` again satisfy the Fermat equation. -/
private lemma fermat_rotate {w t a : K} (h : w ^ 3 + t ^ 3 = 1) (ha : a ^ 3 = 1) :
    (a * w) ^ 3 + (a ^ 2 * t) ^ 3 = 1 := by
  linear_combination (w ^ 3 + t ^ 3 * (a ^ 3 + 1)) * ha + h

omit [DecidableEq K] in
/-- Affine Fermat points with equal coordinates are equal, whatever proof of the
Fermat equation each carries. -/
lemma pt_congr {w t w' t' : K} (h : w ^ 3 + t ^ 3 = 1) (h' : w' ^ 3 + t' ^ 3 = 1)
    (hw : w = w') (ht : t = t') : pt w t h = pt w' t' h' := by
  subst hw; subst ht; rfl

/-- **The diagonal translation formula**: `(w,t) + P_a = (a*w, a^{-1}*t)`. -/
theorem add_ptInf {w t a : K} (h : w ^ 3 + t ^ 3 = 1) (ha : a ^ 3 = 1) :
    pt w t h + ptInf a ha = pt (a * w) (a ^ 2 * t) (fermat_rotate h ha) := by
  by_cases ha1 : a = 1
  · subst ha1
    rw [ptInf_one, add_zero]
    exact pt_congr _ _ (by ring) (by ring)
  · have ha2 := cube_root_rel ha ha1
    have hd := den_ne_zero h
    have hx : ((w + t)⁻¹ : K) ≠ 0 := inv_ne_zero hd
    obtain ⟨m, hmdef⟩ : ∃ m : K, m = a * w + a ^ 2 * t := ⟨_, rfl⟩
    -- the key polynomial identity (P)
    have hP : ((w + a * (w + t)) ^ 2 * (w + t) + 1) * m = w + t := by
      rw [hmdef]
      linear_combination
        (t * a + 5 * t * a ^ 2 + 5 * t * a ^ 3 + t * a ^ 4 + w * a + 2 * w * a ^ 2
          + w * a ^ 3) * h
        + (t + 4 * t * a + t * a ^ 2 + (-5) * t ^ 4 * a + w + w * a + (-4) * w * t ^ 3
          + (-1) * w * t ^ 3 * a + 3 * w * t ^ 3 * a ^ 2 + (-4) * w ^ 2 * t ^ 2
          + 4 * w ^ 2 * t ^ 2 * a + 3 * w ^ 2 * t ^ 2 * a ^ 2) * ha2
        + ((-1) * t + (-2) * t * a + 2 * t ^ 4 * a + (-1) * w + 2 * w * t ^ 3
          + 2 * w * t ^ 3 * a + 2 * w ^ 2 * t ^ 2) * CharTwo.two_eq_zero (R := K)
    have hm : m ≠ 0 := by
      intro hc
      rw [hc, mul_zero] at hP
      exact hd hP.symm
    have hsl : (fer K).toAffine.slope ((w + t)⁻¹) 0 (w * (w + t)⁻¹) a
        = w + a * (w + t) := by
      rw [slope_ne hx]
      field_simp
      ring
    have hX3 : (fer K).toAffine.addX ((w + t)⁻¹) 0
        ((fer K).toAffine.slope ((w + t)⁻¹) 0 (w * (w + t)⁻¹) a)
        = (a * w + a ^ 2 * t)⁻¹ := by
      rw [addX_eq, hsl, ← hmdef]
      field_simp
      linear_combination hP
    rw [pt, ptInf_ne_one ha ha1, Affine.Point.add_of_X_ne hx, pt]
    refine some_eq_some _ _ hX3 ?_
    rw [addY_eq, hX3, hsl, ← hmdef]
    have hQ : (w + a * (w + t)) * ((w + t) + (a * w + a ^ 2 * t)) + w * (a * w + a ^ 2 * t)
        + (w + t) * (a * w + a ^ 2 * t) = a * w * (w + t) := by
      linear_combination (t ^ 2 * a + 3 * w * t + w * t * a + w ^ 2) * ha2
        + ((-1) * w * t + (-1) * w * t * a + w ^ 2 * a) * CharTwo.two_eq_zero (R := K)
    field_simp
    rw [hmdef]
    linear_combination hQ

end KasamiCyclicAdditive.FermatCubic
