/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.WeightedChildren

/-! # Averages -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# Averages

Cube-average algebra used by the first Section 5.3 lemma.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Integrability on a cube gives integrability with respect to the normalized
cube measure. -/
theorem integrable_normalizedCubeMeasure_of_integrableOn_cubeSet
    {d : ℕ} (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q) volume) :
    Integrable f (normalizedCubeMeasure Q) := by
  have hscale_ne_zero : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  change Integrable f (normalizedCubeMeasure Q)
  rw [normalizedCubeMeasure, cubeMeasure]
  exact
    (integrable_smul_measure
      (μ := volume.restrict (cubeSet Q))
      hscale_ne_zero ENNReal.ofReal_ne_top).2 hf

/-- Linearity of cube averages under cube-set integrability hypotheses. -/
theorem cubeAverage_add_of_integrableOn
    {d : ℕ} (Q : TriadicCube d) (f g : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet Q) volume)
    (hg : IntegrableOn g (cubeSet Q) volume) :
    cubeAverage Q (fun x => f x + g x) = cubeAverage Q f + cubeAverage Q g := by
  have hf_norm : Integrable f (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q hf
  have hg_norm : Integrable g (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q hg
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [integral_add hf_norm hg_norm]

/-- The public Ch2 average on an open cube agrees with `cubeAverage`. -/
theorem ch02_average_cubeDomain_eq_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    Ch02.average (Ch02.cubeDomain Q) f = cubeAverage Q f := by
  unfold Ch02.average cubeAverage
  rw [Ch02.cubeDomain_coe]
  rw [← setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := Q) (f := f)]
  rw [volume_openCubeSet_toReal]

/-- Scalar cutoff insertion behind the centered energy splitting. -/
theorem integral_sub_const_eq_integral_cutoff_centered_add_integral_one_sub_cutoff_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ F : α → ℝ} {c : ℝ}
    (hF_int : Integrable F μ)
    (hφ_int : Integrable φ μ)
    (hCut_int : Integrable (fun x => φ x * (F x - c)) μ)
    (hRem_int : Integrable (fun x => (1 - φ x) * F x) μ)
    (hMean : ∫ x, φ x ∂μ = 1) :
    ∫ x, F x ∂μ - c =
      ∫ x, φ x * (F x - c) ∂μ +
        ∫ x, (1 - φ x) * F x ∂μ := by
  have hpoint :
      (fun x => φ x * (F x - c) + (1 - φ x) * F x) =
        fun x => F x - c * φ x := by
    funext x
    ring
  calc
    ∫ x, F x ∂μ - c
        = ∫ x, F x ∂μ - c * ∫ x, φ x ∂μ := by
            rw [hMean]
            ring
    _ = ∫ x, F x ∂μ - ∫ x, c * φ x ∂μ := by
          rw [integral_const_mul]
    _ = ∫ x, F x - c * φ x ∂μ := by
          rw [integral_sub hF_int (hφ_int.const_mul c)]
    _ = ∫ x, φ x * (F x - c) + (1 - φ x) * F x ∂μ := by
          rw [hpoint]
    _ =
      ∫ x, φ x * (F x - c) ∂μ +
        ∫ x, (1 - φ x) * F x ∂μ := by
          rw [integral_add hCut_int hRem_int]

/-- Cube-average form of mean-one cutoff insertion. -/
theorem cubeAverage_sub_const_eq_cubeAverage_cutoff_centered_add_cubeAverage_one_sub_cutoff_mul
    {d : ℕ} (Q : TriadicCube d) {φ F : Vec d → ℝ} {c : ℝ}
    (hF_int : Integrable F (normalizedCubeMeasure Q))
    (hφ_int : Integrable φ (normalizedCubeMeasure Q))
    (hCut_int :
      Integrable (fun x => φ x * (F x - c)) (normalizedCubeMeasure Q))
    (hRem_int :
      Integrable (fun x => (1 - φ x) * F x) (normalizedCubeMeasure Q))
    (hMean : cubeAverage Q φ = 1) :
    cubeAverage Q F - c =
      cubeAverage Q (fun x => φ x * (F x - c)) +
        cubeAverage Q (fun x => (1 - φ x) * F x) := by
  have hMeanInt : ∫ x, φ x ∂ normalizedCubeMeasure Q = 1 := by
    rwa [cubeAverage_eq_integral_normalizedCubeMeasure] at hMean
  simpa [cubeAverage_eq_integral_normalizedCubeMeasure] using
    integral_sub_const_eq_integral_cutoff_centered_add_integral_one_sub_cutoff_mul
      (μ := normalizedCubeMeasure Q) (φ := φ) (F := F) (c := c)
      hF_int hφ_int hCut_int hRem_int hMeanInt

/-- On a child cube, the leftover cutoff factor decomposes as
`1 - φ = ((φ)_R - φ) + (1 - (φ)_R)`. -/
theorem cubeAverage_one_sub_cutoff_mul_eq_cutoff_oscillation_add_mean_defect
    {d : ℕ} (R : TriadicCube d) (φ F : Vec d → ℝ)
    (hOsc :
      IntegrableOn
        (fun x => (cubeAverage R φ - φ x) * F x)
        (cubeSet R) volume)
    (hF : IntegrableOn F (cubeSet R) volume) :
    cubeAverage R (fun x => (1 - φ x) * F x) =
      cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x) +
        (1 - cubeAverage R φ) * cubeAverage R F := by
  have hOsc_norm :
      Integrable
        (fun x => (cubeAverage R φ - φ x) * F x)
        (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R hOsc
  have hMeanDef_norm :
      Integrable
        (fun x => (1 - cubeAverage R φ) * F x)
        (normalizedCubeMeasure R) :=
    (integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R hF).const_mul
      (1 - cubeAverage R φ)
  calc
    cubeAverage R (fun x => (1 - φ x) * F x)
        = ∫ x, (1 - φ x) * F x ∂ normalizedCubeMeasure R := by
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ =
        ∫ x,
          (cubeAverage R φ - φ x) * F x +
            (1 - cubeAverage R φ) * F x ∂ normalizedCubeMeasure R := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun x => by ring
    _ =
        ∫ x, (cubeAverage R φ - φ x) * F x ∂ normalizedCubeMeasure R +
          ∫ x, (1 - cubeAverage R φ) * F x ∂ normalizedCubeMeasure R := by
          rw [integral_add hOsc_norm hMeanDef_norm]
    _ =
        cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x) +
          (1 - cubeAverage R φ) * cubeAverage R F := by
          rw [cubeAverage_eq_integral_normalizedCubeMeasure,
            cubeAverage_eq_integral_normalizedCubeMeasure,
            integral_const_mul]
          rw [cubeAverage_eq_integral_normalizedCubeMeasure]

/-- Descendant partition of the leftover cutoff energy term. -/
theorem cubeAverage_one_sub_cutoff_mul_eq_descendantsAverage_cutoff_oscillation_add_mean_defect
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (φ F : Vec d → ℝ)
    (hRem :
      IntegrableOn
        (fun x => (1 - φ x) * F x) (cubeSet Q) volume)
    (hOsc :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x => (cubeAverage R φ - φ x) * F x)
          (cubeSet R) volume)
    (hF :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn F (cubeSet R) volume) :
    cubeAverage Q (fun x => (1 - φ x) * F x) =
      descendantsAverage Q j fun R =>
        cubeAverage R (fun x => (cubeAverage R φ - φ x) * F x) +
          (1 - cubeAverage R φ) * cubeAverage R F := by
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := fun x => (1 - φ x) * F x) hRem]
  unfold descendantsAverage
  refine congrArg (fun t => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  exact
    cubeAverage_one_sub_cutoff_mul_eq_cutoff_oscillation_add_mean_defect
      R φ F (hOsc R hR) (hF R hR)

/-- Congruence for descendant averages at a fixed depth. -/
theorem descendantsAverage_congr_of_eq_on_descendants {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) {F G : TriadicCube d → ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, F R = G R) :
    descendantsAverage Q j F = descendantsAverage Q j G := by
  unfold descendantsAverage
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum F =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum G
  congr 1
  exact Finset.sum_congr rfl h

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
