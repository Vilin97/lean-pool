/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.InternalModel
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterMonotonicity
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeterTransform

/-!
# Cauchy–Crofton bridge: basic set-up

This module fixes the two perimeter functionals compared by the bridge theorem:

* `hPerimeter K = μH[1] (frontier K)`, the one-dimensional Hausdorff measure of the
  topological boundary;
* `cPerimeter K = ENNReal.ofReal (perimeter K)`, the project's Cauchy width-integral
  perimeter, coerced to `ℝ≥0∞`.

It records their behaviour under translations and positive dilations and an elementary
squeeze lemma in `ℝ≥0∞`.
-/

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

abbrev Point2 := NRR.HumanExport.Plane
abbrev Body := NRR.Geometry.ConvexBody Point2

/-- Hausdorff perimeter: the one-dimensional Hausdorff measure of the topological boundary. -/
def hPerimeter (K : Body) : ENNReal :=
  (μH[1] : Measure Point2) (frontier (K : Set Point2))

/-- The project's real-valued Cauchy perimeter, coerced to `ℝ≥0∞`. -/
def cPerimeter (K : Body) : ENNReal :=
  ENNReal.ofReal (NRR.Geometry.ConvexBody.perimeter K)

theorem hPerimeter_def (K : Body) :
    hPerimeter K = (μH[1] : Measure Point2) (frontier (K : Set Point2)) := rfl

theorem cPerimeter_ne_top (K : Body) : cPerimeter K ≠ ⊤ := by
  simp [cPerimeter]

/-- Monotonicity of the Cauchy perimeter. -/
theorem cPerimeter_mono {K L : Body} (hKL : (K : Set Point2) ⊆ (L : Set Point2)) :
    cPerimeter K ≤ cPerimeter L :=
  ENNReal.ofReal_le_ofReal (NRR.Geometry.planarPerimeter_mono hKL)

/-- Dilation law for the Cauchy perimeter. -/
theorem cPerimeter_scalePos (K : Body) {r : ℝ} (hr : 0 < r) :
    cPerimeter (K.scalePos r hr) = ENNReal.ofReal r * cPerimeter K := by
  simp only [cPerimeter, NRR.Geometry.ConvexBody.perimeter_def,
    NRR.Geometry.planarPerimeter_scalePos]
  rw [ENNReal.ofReal_mul hr.le]

/-- Translation invariance of the Cauchy perimeter. -/
theorem cPerimeter_translate (K : Body) (a : Point2) :
    cPerimeter (K.translate a) = cPerimeter K := by
  simp only [cPerimeter, NRR.Geometry.ConvexBody.perimeter_def,
    NRR.Geometry.planarPerimeter_translate]

/-- Dilation law for the Hausdorff perimeter. -/
theorem hPerimeter_scalePos (K : Body) {r : ℝ} (hr : 0 < r) :
    hPerimeter (K.scalePos r hr) = ENNReal.ofReal r * hPerimeter K := by
  have hcar : (K.scalePos r hr : Set Point2) = r • (K : Set Point2) := rfl
  have hfront : frontier ((K.scalePos r hr : Set Point2)) = r • frontier (K : Set Point2) := by
    rw [hcar]
    have := (Homeomorph.smulOfNeZero r hr.ne').image_frontier (K : Set Point2)
    simpa [Set.image_smul] using this.symm
  rw [hPerimeter, hPerimeter, hfront,
    MeasureTheory.Measure.hausdorffMeasure_smul₀ (d := (1 : ℝ)) zero_le_one hr.ne']
  simp [ENNReal.smul_def, Real.nnnorm_of_nonneg hr.le,
    ENNReal.ofReal_eq_coe_nnreal hr.le]

/-- Translation invariance of the Hausdorff perimeter. -/
theorem hPerimeter_translate (K : Body) (a : Point2) :
    hPerimeter (K.translate a) = hPerimeter K := by
  have hfront : frontier ((K.translate a : Set Point2))
      = (fun x => a + x) '' frontier (K : Set Point2) := by
    rw [NRR.Geometry.ConvexBody.translate_carrier]
    exact ((Homeomorph.addLeft a).image_frontier (K : Set Point2)).symm
  rw [hPerimeter, hPerimeter, hfront]
  have hiso : Isometry (fun x : Point2 => a + x) :=
    Isometry.of_dist_eq (fun x y => by simp [dist_eq_norm, add_sub_add_left_eq_sub])
  exact hiso.hausdorffMeasure_image (Or.inl zero_le_one) _

/-- Elementary real-number squeeze. -/
private theorem real_le_of_forall_one_lt_mul {A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ r : ℝ, 1 < r → A ≤ r * B) : A ≤ B := by
  rcases eq_or_lt_of_le hB with hB0 | hB0
  · have h2 := h 2 (by norm_num)
    nlinarith
  · by_contra hlt
    push Not at hlt
    have hone : 1 < A / B := (one_lt_div hB0).2 hlt
    have hr : 1 < (A / B + 1) / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have hle := h _ hr
    have h2 : (A / B + 1) / 2 * B < A := by
      rw [div_mul_eq_mul_div, add_mul, div_mul_cancel₀ _ hB0.ne']
      linarith
    linarith

/-- Squeeze lemma: if `a ≤ r * b` and `b ≤ r * a` for every `r > 1`, then `a = b`. -/
theorem eq_of_forall_one_lt_mul
    {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hab : ∀ r : ℝ, 1 < r → a ≤ ENNReal.ofReal r * b)
    (hba : ∀ r : ℝ, 1 < r → b ≤ ENNReal.ofReal r * a) : a = b := by
  apply (ENNReal.toReal_eq_toReal_iff' ha hb).mp
  refine le_antisymm ?_ ?_
  · refine real_le_of_forall_one_lt_mul ENNReal.toReal_nonneg (fun r hr => ?_)
    have h := ENNReal.toReal_mono (by
      simp [ENNReal.mul_eq_top, hb, ENNReal.ofReal_ne_top]) (hab r hr)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_trans zero_le_one hr.le)] at h
  · refine real_le_of_forall_one_lt_mul ENNReal.toReal_nonneg (fun r hr => ?_)
    have h := ENNReal.toReal_mono (by
      simp [ENNReal.mul_eq_top, ha, ENNReal.ofReal_ne_top]) (hba r hr)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_trans zero_le_one hr.le)] at h

end HumanVerification.CauchyCrofton
