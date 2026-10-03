/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.WeakForm
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.H10Function

/-!
# Local block energy: the squared cutoff `η²`

Smoothness, `[0,1]`-bounds, and the product-rule gradient
`∂ᵢ(η²) = 2 η ∂ᵢη` for the squared cutoff, together with the `L^∞`
memberships (on a finite-measure domain) needed to feed the library's smooth×`H¹`
product constructions.
-/

@[expose] public section

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The squared cutoff. -/
def sqCutoff (η : Vec d → ℝ) : Vec d → ℝ := fun x => (η x) ^ 2

@[simp] theorem sqCutoff_apply (η : Vec d → ℝ) (x : Vec d) :
    sqCutoff η x = (η x) ^ 2 := rfl

theorem sqCutoff_contDiff {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) (sqCutoff η) := by
  have : sqCutoff η = fun x => η x * η x := by funext x; rw [sqCutoff_apply, pow_two]
  rw [this]; exact hη.mul hη

theorem sqCutoff_nonneg (η : Vec d → ℝ) (x : Vec d) : 0 ≤ sqCutoff η x := by
  rw [sqCutoff_apply]; positivity

theorem sqCutoff_le_one {η : Vec d → ℝ} (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (x : Vec d) : sqCutoff η x ≤ 1 := by
  rw [sqCutoff_apply]
  have h := hη x
  rw [Set.mem_Icc] at h
  nlinarith [h.1, h.2]

theorem abs_sqCutoff_le_one {η : Vec d → ℝ} (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (x : Vec d) : |sqCutoff η x| ≤ 1 := by
  rw [abs_of_nonneg (sqCutoff_nonneg η x)]
  exact sqCutoff_le_one hη x

/-- The product-rule gradient of `η²`: `∂ᵢ(η²) = 2 η ∂ᵢη`. -/
theorem fderiv_sqCutoff {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (x : Vec d)
    (i : Fin d) :
    fderiv ℝ (sqCutoff η) x (basisVec i) = 2 * η x * fderiv ℝ η x (basisVec i) := by
  have hdiff : DifferentiableAt ℝ η x := (hη.contDiffAt).differentiableAt (by simp)
  have hd : HasFDerivAt η (fderiv ℝ η x) x := hdiff.hasFDerivAt
  have hsq : HasFDerivAt (sqCutoff η)
      (η x • fderiv ℝ η x + η x • fderiv ℝ η x) x := by
    have hrw : sqCutoff η = fun y => η y * η y := by funext y; rw [sqCutoff_apply, pow_two]
    rw [hrw]; exact hd.mul hd
  rw [hsq.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The support of `η²` equals the support of `η`. -/
theorem support_sqCutoff (η : Vec d → ℝ) :
    Function.support (sqCutoff η) = Function.support η := by
  ext x
  simp only [Function.mem_support, sqCutoff_apply, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
    not_false_eq_true]

/-! ## `L^∞` memberships on a finite-measure domain -/

variable {U : Set (Vec d)}

theorem memLpTop_sqCutoff {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (sqCutoff η) (⊤ : ENNReal) (volume.restrict U) := by
  refine MeasureTheory.memLp_top_of_bound
    (sqCutoff_contDiff hη).continuous.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall (fun x => abs_sqCutoff_le_one hIcc x)

theorem memLpTop_fderiv_sqCutoff {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) {Gη : ℝ}
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) (i : Fin d) :
    MemLp (fun x => (fderiv ℝ (sqCutoff η) x) (basisVec i)) (⊤ : ENNReal)
      (volume.restrict U) := by
  have hcont : Continuous (fun x => (fderiv ℝ (sqCutoff η) x) (basisVec i)) := by
    have := (sqCutoff_contDiff hη).continuous_fderiv (by simp)
    exact this.clm_apply continuous_const
  refine MeasureTheory.memLp_top_of_bound hcont.aestronglyMeasurable (2 * Gη) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [fderiv_sqCutoff hη x i]
  have hη1 : |η x| ≤ 1 := by
    have h := hIcc x; rw [Set.mem_Icc] at h
    rw [abs_of_nonneg h.1]; exact h.2
  calc |2 * η x * fderiv ℝ η x (basisVec i)|
      = 2 * |η x| * |fderiv ℝ η x (basisVec i)| := by
        rw [abs_mul, abs_mul]; simp
    _ ≤ 2 * 1 * Gη := by
        have hGnn : 0 ≤ Gη := le_trans (abs_nonneg _) (hGη x i)
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left hη1 (by norm_num)
        · exact hGη x i
        · exact abs_nonneg _
        · positivity
    _ = 2 * Gη := by ring

end

end Homogenization
