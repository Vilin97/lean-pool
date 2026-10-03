/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-! Vector L2 triangle inequality with a narrow analysis import. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError

theorem RelativeVectorTriangle.quadratic_cross_bound {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * R + B) :
    R ≤ Real.sqrt A * Real.sqrt B := by
  have hs : R ^ 2 ≤ A * B := by
    by_cases ha : A = 0
    · have hr : R = 0 := by
        by_contra hR
        have ht := hp ((B + 1) / (2 * R))
        rw [ha] at ht
        have he : 2 * ((B + 1) / (2 * R)) * R = B + 1 := by field_simp
        rw [he] at ht
        linarith only [ht]
      simp only [ha, hr, zero_pow (by norm_num : 2 ≠ 0), zero_mul, le_refl]
    · have hap : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
      have ht := mul_nonneg (sq_nonneg A) (hp (R / A))
      have he : A ^ 2 * ((R / A) ^ 2 * A - 2 * (R / A) * R + B) =
          A * (A * B - R ^ 2) := by field_simp; ring
      rw [he] at ht
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hap).mp ht)
  have hsq : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  apply (le_abs_self R).trans
  apply (sq_le_sq₀ (abs_nonneg R) (by positivity : 0 ≤ Real.sqrt A * Real.sqrt B)).mp
  simpa only [sq_abs, hsq] using hs

/-- The integral L2 triangle inequality for the actual `Vec 2` carrier. -/
theorem relative_vector_integral_L2_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → Vec 2}
    (hf : Integrable (fun x => vecNormSq (f x)) μ)
    (hg : Integrable (fun x => vecNormSq (g x)) μ)
    (hfg : Integrable (fun x => vecDot (f x) (g x)) μ) :
    Real.sqrt (∫ x, vecNormSq (f x + g x) ∂μ) ≤
      Real.sqrt (∫ x, vecNormSq (f x) ∂μ) + Real.sqrt (∫ x, vecNormSq (g x) ∂μ) := by
  let A := ∫ x, vecNormSq (f x) ∂μ
  let B := ∫ x, vecNormSq (g x) ∂μ
  let R := ∫ x, vecDot (f x) (g x) ∂μ
  have hnonneg (v : Vec 2) : 0 ≤ vecNormSq v := by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hA : 0 ≤ A := integral_nonneg (fun x => hnonneg (f x))
  have hB : 0 ≤ B := integral_nonneg (fun x => hnonneg (g x))
  have hp (t : ℝ) : 0 ≤ t ^ 2 * A - 2 * t * R + B := by
    have he : (fun x => t ^ 2 * vecNormSq (f x) - 2 * t * vecDot (f x) (g x) + vecNormSq (g x)) =
        (fun x => vecNormSq (t • f x - g x)) := by
      funext x
      simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hn : 0 ≤ ∫ x, vecNormSq (t • f x - g x) ∂μ :=
      integral_nonneg (fun x => hnonneg (t • f x - g x))
    have hs := integral_add ((hf.const_mul (t ^ 2)).sub (hfg.const_mul (2 * t))) hg
    have ht := integral_sub (hf.const_mul (t ^ 2)) (hfg.const_mul (2 * t))
    dsimp only [Pi.add_apply, Pi.sub_apply] at hs ht
    rw [← he, hs, ht, integral_const_mul, integral_const_mul] at hn
    exact hn
  have hR := RelativeVectorTriangle.quadratic_cross_bound hA hB hp
  have he : (∫ x, vecNormSq (f x + g x) ∂μ) = A + 2 * R + B := by
    have he : (fun x => vecNormSq (f x + g x)) =
        (fun x => vecNormSq (f x) + 2 * vecDot (f x) (g x) + vecNormSq (g x)) := by
      funext x
      simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.add_apply]
      ring
    have hs := integral_add (hf.add (hfg.const_mul (2 : ℝ))) hg
    have ht := integral_add hf (hfg.const_mul (2 : ℝ))
    dsimp only [Pi.add_apply] at hs ht
    rw [he, hs, ht, integral_const_mul]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [he]
    nlinarith only [hR, Real.sq_sqrt hA, Real.sq_sqrt hB]

end AVenhance.Infra.Section5.RelativeError
