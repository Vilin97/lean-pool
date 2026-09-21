/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Euclidean
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Norm Scaling -/

open scoped Pointwise ENNReal

namespace Homogenization
namespace Book
namespace Ch01

/-!
# Scaling of normalized averages

These are the Chapter 1 bookkeeping lemmas for dilation.  The main use in
Chapter 3 is the last theorem: a unit-scale estimate for the pulled-back
gradient transfers to the physical cube with the expected `r^{-2}` factor on
the right-hand side.
-/

noncomputable section

/-- Normalized volume averages are invariant under translation of the domain,
with the function pulled back by the inverse translation. -/
theorem volumeAverage_translateSet_comp_subRight {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (translateSet z U) (fun x => f (x - z)) =
      volumeAverage U f := by
  unfold volumeAverage
  rw [volume_translateSet_eq]
  congr 1
  exact setIntegral_comp_subRight_translateSet (d := d) (E := ℝ) z U f

/-- Equivalent forward form of translation invariance for normalized volume
averages. -/
theorem volumeAverage_translateSet_eq_comp_addRight {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (translateSet z U) f =
      volumeAverage U (fun x => f (x + z)) := by
  unfold volumeAverage
  rw [volume_translateSet_eq]
  congr 1
  symm
  exact setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U f

/-- Scalar normalized `L²` square is invariant under translation of the domain,
with the scalar field pulled back. -/
theorem volumeAverage_sq_translateSet_comp_subRight {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (u : Vec d → ℝ) :
    volumeAverage (translateSet z U) (fun x => u (x - z) ^ (2 : ℕ)) =
      volumeAverage U (fun x => u x ^ (2 : ℕ)) := by
  simpa using
    volumeAverage_translateSet_comp_subRight (d := d) z U
      (fun x => u x ^ (2 : ℕ))

/-- Vector normalized `L²` square is invariant under translation of the domain,
with the vector field pulled back. -/
theorem volumeAverage_vecNormSq_translateSet_comp_subRight {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) (G : Vec d → Vec d) :
    volumeAverage (translateSet z U) (fun x => vecNormSq (G (x - z))) =
      volumeAverage U (fun x => vecNormSq (G x)) := by
  simpa using
    volumeAverage_translateSet_comp_subRight (d := d) z U
      (fun x => vecNormSq (G x))

/-- Lebesgue volume of a positive dilation, written in `toReal` form. -/
theorem volume_smul_toReal_of_pos {d : ℕ} {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) :
    (MeasureTheory.volume (r • U)).toReal =
      r ^ d * (MeasureTheory.volume U).toReal := by
  have hmeasure :
      MeasureTheory.volume (r • U) =
        ENNReal.ofReal (r ^ d) * MeasureTheory.volume U := by
    simpa [Vec] using
      (MeasureTheory.Measure.addHaar_smul_of_nonneg
        (μ := MeasureTheory.volume) (E := Vec d) hr.le U)
  rw [hmeasure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le d)]

/-- Normalized volume averages are invariant under positive dilation of the
domain, with the function pulled back by the dilation map. -/
theorem volumeAverage_smul_set_comp_smul_of_pos {d : ℕ} {r : ℝ}
    (hr : 0 < r) (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (r • U) f =
      volumeAverage U (fun x => f (r • x)) := by
  have hvol := volume_smul_toReal_of_pos (d := d) hr U
  have hscale_pos : 0 < r ^ d := pow_pos hr d
  have hsetIntegral :
      ∫ x in U, f (r • x) ∂MeasureTheory.volume =
        (r ^ d)⁻¹ * ∫ y in r • U, f y ∂MeasureTheory.volume := by
    simpa [Vec, smul_eq_mul] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := f) (s := U) hr)
  unfold volumeAverage
  rw [hsetIntegral, hvol]
  by_cases hU_zero : (MeasureTheory.volume U).toReal = 0
  · simp [hU_zero]
  · field_simp [hU_zero, hscale_pos.ne']

/-- Raw set-integral form of positive dilation change of variables. -/
theorem setIntegral_comp_smul_of_pos {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in U, f (r • x) ∂MeasureTheory.volume =
      (r ^ d)⁻¹ • ∫ y in r • U, f y ∂MeasureTheory.volume := by
  simpa [Vec] using
    (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      (μ := MeasureTheory.volume) (f := f) (s := U) hr)

/-- Forward raw set-integral form of positive dilation change of variables. -/
theorem setIntegral_smul_set_eq_comp_smul_of_pos {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in r • U, f y ∂MeasureTheory.volume =
      r ^ d • ∫ x in U, f (r • x) ∂MeasureTheory.volume := by
  have hcomp := setIntegral_comp_smul_of_pos (d := d) (E := E) hr U f
  have hpow_ne : r ^ d ≠ 0 := pow_ne_zero d hr.ne'
  calc
    ∫ y in r • U, f y ∂MeasureTheory.volume =
        r ^ d • ((r ^ d)⁻¹ • ∫ y in r • U, f y ∂MeasureTheory.volume) := by
          rw [smul_smul, mul_inv_cancel₀ hpow_ne, one_smul]
    _ = r ^ d • ∫ x in U, f (r • x) ∂MeasureTheory.volume := by
          rw [hcomp]

/--
Raw set-integral form of a positive dilation followed by translation.
-/
theorem setIntegral_translateSet_smul_set_eq_comp_affine_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (z : Vec d) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ y in translateSet z (r • U), f y ∂MeasureTheory.volume =
      r ^ d • ∫ x in U, f (r • x + z) ∂MeasureTheory.volume := by
  calc
    ∫ y in translateSet z (r • U), f y ∂MeasureTheory.volume =
        ∫ y in r • U, f (y + z) ∂MeasureTheory.volume := by
          exact (setIntegral_comp_addRight_translateSet
            (d := d) (E := E) z (r • U) f).symm
    _ = r ^ d • ∫ x in U, f (r • x + z) ∂MeasureTheory.volume :=
          setIntegral_smul_set_eq_comp_smul_of_pos
            (d := d) (E := E) hr U (fun y => f (y + z))

/-- Raw set integrals over explicit Euclidean balls reduce to unit-ball
integrals by affine pullback. -/
theorem setIntegral_euclideanBall_eq_unit_affine_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (z : Vec d) (f : Vec d → E) :
    ∫ y in euclideanBall z r, f y ∂MeasureTheory.volume =
      r ^ d • ∫ x in euclideanBall (0 : Vec d) 1,
        f (r • x + z) ∂MeasureTheory.volume := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos z hr]
  exact setIntegral_translateSet_smul_set_eq_comp_affine_of_pos
    (d := d) (E := E) hr z (euclideanBall (0 : Vec d) 1) f

/-- Scalar normalized `L²` square is invariant under positive dilation of the
domain, with the scalar field pulled back. -/
theorem volumeAverage_sq_comp_smul_of_pos {d : ℕ} {r : ℝ}
    (hr : 0 < r) (U : Set (Vec d)) (u : Vec d → ℝ) :
    volumeAverage (r • U) (fun y => u y ^ (2 : ℕ)) =
      volumeAverage U (fun x => u (r • x) ^ (2 : ℕ)) := by
  simpa using
    volumeAverage_smul_set_comp_smul_of_pos (d := d) hr U
      (fun y => u y ^ (2 : ℕ))

/-- Vector normalized `L²` square is invariant under positive dilation of the
domain, with the vector field pulled back. -/
theorem volumeAverage_vecNormSq_comp_smul_of_pos {d : ℕ} {r : ℝ}
    (hr : 0 < r) (U : Set (Vec d)) (G : Vec d → Vec d) :
    volumeAverage (r • U) (fun y => vecNormSq (G y)) =
      volumeAverage U (fun x => vecNormSq (G (r • x))) := by
  simpa using
    volumeAverage_smul_set_comp_smul_of_pos (d := d) hr U
      (fun y => vecNormSq (G y))

/-- Normalized volume averages are invariant under a positive dilation followed
by a translation. -/
theorem volumeAverage_translateSet_smul_set_comp_affine_of_pos {d : ℕ}
    {r : ℝ} (hr : 0 < r) (z : Vec d) (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (translateSet z (r • U)) f =
      volumeAverage U (fun x => f (r • x + z)) := by
  calc
    volumeAverage (translateSet z (r • U)) f =
        volumeAverage (r • U) (fun y => f (y + z)) :=
      volumeAverage_translateSet_eq_comp_addRight z (r • U) f
    _ = volumeAverage U (fun x => f (r • x + z)) :=
      volumeAverage_smul_set_comp_smul_of_pos (d := d) hr U
        (fun y => f (y + z))

/--
Normalized averages over explicit Euclidean balls reduce to unit-ball
averages by affine pullback.
-/
theorem volumeAverage_euclideanBall_eq_unit_affine_of_pos {d : ℕ}
    {r : ℝ} (hr : 0 < r) (z : Vec d) (f : Vec d → ℝ) :
    volumeAverage (euclideanBall z r) f =
      volumeAverage (euclideanBall (0 : Vec d) 1) (fun x => f (r • x + z)) := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos z hr]
  exact volumeAverage_translateSet_smul_set_comp_affine_of_pos
    (d := d) hr z (euclideanBall (0 : Vec d) 1) f

/--
Normalized averages over explicit closed Euclidean balls reduce to unit-ball
averages by affine pullback.
-/
theorem volumeAverage_euclideanClosedBall_eq_unit_affine_of_pos {d : ℕ}
    {r : ℝ} (hr : 0 < r) (z : Vec d) (f : Vec d → ℝ) :
    volumeAverage (euclideanClosedBall z r) f =
      volumeAverage (euclideanClosedBall (0 : Vec d) 1) (fun x => f (r • x + z)) := by
  rw [euclideanClosedBall_eq_translateSet_smul_unit_of_pos z hr]
  exact volumeAverage_translateSet_smul_set_comp_affine_of_pos
    (d := d) hr z (euclideanClosedBall (0 : Vec d) 1) f

/-- Inverse-pullback form of affine invariance for normalized averages. -/
theorem volumeAverage_translateSet_smul_set_comp_inv_affine_of_pos {d : ℕ}
    {r : ℝ} (hr : 0 < r) (z : Vec d) (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (translateSet z (r • U))
        (fun y => f (r⁻¹ • (y - z))) =
      volumeAverage U f := by
  rw [volumeAverage_translateSet_smul_set_comp_affine_of_pos (d := d) hr z U]
  congr 1
  funext x
  have hr_ne : r ≠ 0 := hr.ne'
  congr 1
  ext i
  simp [Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, hr_ne]

/-- Scalar normalized `L²` square is invariant under a positive dilation
followed by a translation, with the scalar field pulled back. -/
theorem volumeAverage_sq_translateSet_smul_set_comp_inv_affine_of_pos {d : ℕ}
    {r : ℝ} (hr : 0 < r) (z : Vec d) (U : Set (Vec d)) (u : Vec d → ℝ) :
    volumeAverage (translateSet z (r • U))
        (fun y => u (r⁻¹ • (y - z)) ^ (2 : ℕ)) =
      volumeAverage U (fun x => u x ^ (2 : ℕ)) := by
  simpa using
    volumeAverage_translateSet_smul_set_comp_inv_affine_of_pos
      (d := d) hr z U (fun x => u x ^ (2 : ℕ))

/-- Vector normalized `L²` square is invariant under a positive dilation
followed by a translation, with the vector field pulled back. -/
theorem volumeAverage_vecNormSq_translateSet_smul_set_comp_inv_affine_of_pos
    {d : ℕ} {r : ℝ} (hr : 0 < r) (z : Vec d) (U : Set (Vec d))
    (G : Vec d → Vec d) :
    volumeAverage (translateSet z (r • U))
        (fun y => vecNormSq (G (r⁻¹ • (y - z)))) =
      volumeAverage U (fun x => vecNormSq (G x)) := by
  simpa using
    volumeAverage_translateSet_smul_set_comp_inv_affine_of_pos
      (d := d) hr z U (fun x => vecNormSq (G x))

/-- Scalar normalized `L²` square after an additional amplitude scaling. -/
theorem volumeAverage_sq_scaled_comp_smul_of_pos {d : ℕ} {r : ℝ}
    (hr : 0 < r) (U : Set (Vec d)) (u : Vec d → ℝ) :
    volumeAverage U (fun x => (r * u (r • x)) ^ (2 : ℕ)) =
      r ^ (2 : ℕ) * volumeAverage (r • U) (fun y => u y ^ (2 : ℕ)) := by
  calc
    volumeAverage U (fun x => (r * u (r • x)) ^ (2 : ℕ)) =
        volumeAverage U (fun x => r ^ (2 : ℕ) * (u (r • x) ^ (2 : ℕ))) := by
      congr 1
      funext x
      ring
    _ = r ^ (2 : ℕ) *
        volumeAverage U (fun x => u (r • x) ^ (2 : ℕ)) := by
      have h : (fun x => r ^ (2 : ℕ) * u (r • x) ^ (2 : ℕ)) =
          r ^ (2 : ℕ) • (fun x => u (r • x) ^ (2 : ℕ)) := by
        funext x
        simp [Pi.smul_apply, smul_eq_mul]
      rw [h]
      exact volumeAverage_smul U (r ^ (2 : ℕ))
        (fun x => u (r • x) ^ (2 : ℕ))
    _ = r ^ (2 : ℕ) *
        volumeAverage (r • U) (fun y => u y ^ (2 : ℕ)) := by
      rw [← volumeAverage_sq_comp_smul_of_pos (d := d) hr U u]

/-- Vector normalized `L²` square after the gradient-style amplitude scaling:
`G` pulls back as `r • G (r • x)`. -/
theorem volumeAverage_vecNormSq_scaled_comp_smul_of_pos {d : ℕ} {r : ℝ}
    (hr : 0 < r) (U : Set (Vec d)) (G : Vec d → Vec d) :
    volumeAverage U (fun x => vecNormSq (r • G (r • x))) =
      r ^ (2 : ℕ) * volumeAverage (r • U) (fun y => vecNormSq (G y)) := by
  calc
    volumeAverage U (fun x => vecNormSq (r • G (r • x))) =
        volumeAverage U (fun x => r ^ (2 : ℕ) * vecNormSq (G (r • x))) := by
      congr 1
      funext x
      rw [vecNormSq_smul]
    _ = r ^ (2 : ℕ) *
        volumeAverage U (fun x => vecNormSq (G (r • x))) := by
      have h : (fun x => r ^ (2 : ℕ) * vecNormSq (G (r • x))) =
          r ^ (2 : ℕ) • (fun x => vecNormSq (G (r • x))) := by
        funext x
        simp [Pi.smul_apply, smul_eq_mul]
      rw [h]
      exact volumeAverage_smul U (r ^ (2 : ℕ))
        (fun x => vecNormSq (G (r • x)))
    _ = r ^ (2 : ℕ) *
        volumeAverage (r • U) (fun y => vecNormSq (G y)) := by
      rw [← volumeAverage_vecNormSq_comp_smul_of_pos (d := d) hr U G]

/-- Transfer a unit-scale Caccioppoli-shaped estimate through a positive
dilation.  The gradient pullback contributes exactly the physical `r^{-2}`
factor on the right-hand side. -/
theorem caccioppoliScale_from_unit_averages {d : ℕ} {r C : ℝ}
    (hr : 0 < r) (U : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hunit :
      volumeAverage U (fun x => vecNormSq (r • G (r • x))) ≤
        C * volumeAverage U (fun x => u (r • x) ^ (2 : ℕ))) :
    volumeAverage (r • U) (fun y => vecNormSq (G y)) ≤
      r⁻¹ ^ (2 : ℕ) * C *
        volumeAverage (r • U) (fun y => u y ^ (2 : ℕ)) := by
  have hgrad :=
    volumeAverage_vecNormSq_scaled_comp_smul_of_pos (d := d) hr U G
  have hu := volumeAverage_sq_comp_smul_of_pos (d := d) hr U u
  have hscaled :
      r ^ (2 : ℕ) *
          volumeAverage (r • U) (fun y => vecNormSq (G y)) ≤
        C * volumeAverage (r • U) (fun y => u y ^ (2 : ℕ)) := by
    simpa [hgrad, ← hu] using hunit
  have hr2_pos : 0 < r ^ (2 : ℕ) := pow_pos hr 2
  calc
    volumeAverage (r • U) (fun y => vecNormSq (G y)) =
        (r ^ (2 : ℕ))⁻¹ *
          (r ^ (2 : ℕ) *
            volumeAverage (r • U) (fun y => vecNormSq (G y))) := by
      field_simp [hr2_pos.ne']
    _ ≤ (r ^ (2 : ℕ))⁻¹ *
        (C * volumeAverage (r • U) (fun y => u y ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hr2_pos.le)
    _ = r⁻¹ ^ (2 : ℕ) * C *
        volumeAverage (r • U) (fun y => u y ^ (2 : ℕ)) := by
      field_simp [hr.ne']

end

end Ch01
end Book
end Homogenization
