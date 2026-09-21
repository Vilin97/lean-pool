/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage3AnchorNorming
import Mathlib.Analysis.Convex.Deriv

/-!
# Stage 3: exact `ell_p -> ell_q` descent lemma

The scalar line restriction is differentiated using the frozen
`IsCoordinateGradient` interface.  After subtracting the exact quadratic
model, its derivative is nonpositive on `[0,1]`; this yields the coefficient
`L/2`, rather than the weaker coefficient obtainable from two convexity
inequalities alone.
-/

namespace O3
namespace Stage3Anchor

noncomputable def objectiveLine {d : ℕ} (f : Vec d → ℝ)
    (x y : Vec d) (t : ℝ) : ℝ :=
  f (AffineMap.lineMap x y t)

lemma hasDerivAt_objectiveLine {d : ℕ} {f : Vec d → ℝ}
    {grad : Vec d → Vec d} (hgrad : IsCoordinateGradient f grad)
    (x y : Vec d) (t : ℝ) :
    HasDerivAt (objectiveLine f x y)
      (pairing (grad (AffineMap.lineMap x y t)) (y - x)) t := by
  have hf := (hgrad (AffineMap.lineMap x y t)).1.hasFDerivAt
  have hline := AffineMap.hasDerivAt_lineMap
    (a := x) (b := y) (x := t)
  have hcomp := hf.comp t hline.hasFDerivAt
  have hscalar := hcomp.hasDerivAt
  have hderivEq :
      ((fderiv ℝ f (AffineMap.lineMap x y t) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (y - x)) 1) =
        pairing (grad (AffineMap.lineMap x y t)) (y - x) := by
    simpa using (hgrad (AffineMap.lineMap x y t)).2 (y - x)
  have hs := hscalar.congr_deriv hderivEq
  change HasDerivAt (f ∘ AffineMap.lineMap x y)
    (pairing (grad (AffineMap.lineMap x y t)) (y - x)) t
  exact hs

/-- Source first-order convexity, derived from convexity and the actual
coordinate representation of the Frechet derivative. -/
theorem firstOrderConvex_of_coordinateGradient {d : ℕ} {f : Vec d → ℝ}
    {grad : Vec d → Vec d} (hconv : IsConvexObjective f)
    (hgrad : IsCoordinateGradient f grad) : FirstOrderConvex f grad := by
  intro x y
  have hlineConv : ConvexOn ℝ Set.univ (objectiveLine f x y) := by
    have hc := hconv.comp_affineMap (AffineMap.lineMap x y)
    change ConvexOn ℝ Set.univ (f ∘ AffineMap.lineMap x y)
    simpa only [Set.preimage_univ] using hc
  have htangent := hlineConv.le_slope_of_hasDerivAt
    (x := (0 : ℝ)) (y := (1 : ℝ)) (by simp) (by simp) (by norm_num)
    (hasDerivAt_objectiveLine hgrad x y 0)
  norm_num [slope, objectiveLine, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at htangent
  linarith

noncomputable def smoothPathRemainder {d : ℕ} (p L : ℝ)
    (f : Vec d → ℝ) (grad : Vec d → Vec d) (x y : Vec d) (t : ℝ) : ℝ :=
  let h := y - x
  objectiveLine f x y t - t * pairing (grad x) h -
    (L / 2) * t ^ (2 : ℕ) * (lpNorm p h) ^ (2 : ℕ)

noncomputable def smoothPathRemainderDeriv {d : ℕ} (p L : ℝ)
    (grad : Vec d → Vec d) (x y : Vec d) (t : ℝ) : ℝ :=
  let h := y - x
  pairing (grad (AffineMap.lineMap x y t)) h - pairing (grad x) h -
    L * t * (lpNorm p h) ^ (2 : ℕ)

lemma hasDerivAt_smoothPathRemainder {d : ℕ} {p L : ℝ}
    {f : Vec d → ℝ} {grad : Vec d → Vec d}
    (hgrad : IsCoordinateGradient f grad) (x y : Vec d) (t : ℝ) :
    HasDerivAt (smoothPathRemainder p L f grad x y)
      (smoothPathRemainderDeriv p L grad x y t) t := by
  let h := y - x
  have hf := hasDerivAt_objectiveLine hgrad x y t
  have hlinear : HasDerivAt (fun s : ℝ ↦ s * pairing (grad x) h)
      (pairing (grad x) h) t := by
    simpa [id_eq] using (hasDerivAt_id t).mul_const (pairing (grad x) h)
  have hquadRaw := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const
    ((lpNorm p h) ^ (2 : ℕ))
  have hquad : HasDerivAt
      (fun s : ℝ ↦ (L / 2) * s ^ (2 : ℕ) * (lpNorm p h) ^ (2 : ℕ))
      (L * t * (lpNorm p h) ^ (2 : ℕ)) t := by
    simp [id_eq] at hquadRaw
    have heq : (L / 2) * (2 * t) * (lpNorm p h) ^ (2 : ℕ) =
        L * t * (lpNorm p h) ^ (2 : ℕ) := by ring
    rw [← heq]
    exact hquadRaw
  exact (hf.sub hlinear).sub hquad

lemma smoothPathRemainderDeriv_nonpos {d : ℕ} {p q L t : ℝ}
    {grad : Vec d → Vec d}
    (hp : 1 < p) (hpq : p.HolderConjugate q)
    (hsmooth : IsLpSmooth p q L grad) (x y : Vec d)
    (ht0 : 0 ≤ t) :
    smoothPathRemainderDeriv p L grad x y t ≤ 0 := by
  let h := y - x
  let z := AffineMap.lineMap x y t
  have hzsub : z - x = t • h := by
    funext i
    simp only [z, h, AffineMap.lineMap_apply_module', Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnorm : lpNorm p (z - x) = t * lpNorm p h := by
    rw [hzsub, Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ p), abs_of_nonneg ht0]
  have hholder := pairing_le_lpNorm_mul hpq.symm (grad z - grad x) h
  have hlip := hsmooth z x
  rw [hnorm] at hlip
  have hnormh : 0 ≤ lpNorm p h := lpNorm_nonneg p h
  have hmul := mul_le_mul_of_nonneg_right hlip hnormh
  have hpairEq :
      pairing (grad z) h - pairing (grad x) h = pairing (grad z - grad x) h := by
    simp only [pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  change pairing (grad z) h - pairing (grad x) h -
      L * t * (lpNorm p h) ^ (2 : ℕ) ≤ 0
  rw [hpairEq]
  nlinarith

/-- Exact source descent lemma with coefficient `L/2`. -/
theorem smooth_descent_lp {d : ℕ} {p q L : ℝ}
    {f : Vec d → ℝ} {grad : Vec d → Vec d}
    (hp : 1 < p) (hpq : p.HolderConjugate q)
    (hgrad : IsCoordinateGradient f grad)
    (hsmooth : IsLpSmooth p q L grad) (x y : Vec d) :
    f y ≤ f x + pairing (grad x) (y - x) +
      (L / 2) * (lpNorm p (y - x)) ^ (2 : ℕ) := by
  let F := smoothPathRemainder p L f grad x y
  let F' := smoothPathRemainderDeriv p L grad x y
  have hderiv : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    exact hasDerivAt_smoothPathRemainder hgrad x y t
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun t ↦
    (hderiv t).continuousAt
  have hanti : AntitoneOn F (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hcont.continuousOn
    · intro t ht
      exact (hderiv t).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
      exact smoothPathRemainderDeriv_nonpos hp hpq hsmooth x y ht'.1.le
  have hend := hanti (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num [F, F', smoothPathRemainder, objectiveLine,
    AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hend
  nlinarith

end Stage3Anchor
end O3
