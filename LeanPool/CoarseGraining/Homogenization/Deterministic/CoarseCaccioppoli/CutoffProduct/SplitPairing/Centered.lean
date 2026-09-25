/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.CenteredProduct

/-! # Centered -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_note_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u g : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bavg Bcirc1 BcircS B C Bg : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hneg1 : ∀ N : ℕ, cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Bcirc1)
    (hnegS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ BcircS)
    (hBg_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg := by
    intro N
    have hpartial :=
      cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_poincare_cutoff_terms
        Q s N u g ξ hB hu (hproj N) hg hξLp hξ hderiv hs0 hs1 hC
    have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
      exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
    have hterm1 :
        cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
          ≤
        cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) := by
      refine mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine mul_le_mul_of_nonneg_left (hneg1 N) ?_
      exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
    have hnoteS_nonneg :
        0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) := by
      have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _))
        (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
    have hterm2inner :
        cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)
          ≤
        cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
              BcircS) := by
      refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg (-s) Q)
      exact mul_le_mul_of_nonneg_left (hnegS N) hnoteS_nonneg
    have hterm2 :
        cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
                cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
          ≤
        cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
                BcircS)) := by
      exact mul_le_mul_of_nonneg_left hterm2inner (cubeLpNorm_nonneg Q ∞ ξ)
    calc
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x)
          ≤
        2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) *
                cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := hpartial
      _ ≤
        2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) := by
              exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
      _ ≤ Bg := hBg_bound
  exact
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_average_note_terms_of_partialBounds_of_projectedDualMeanZeroPoincareEstimate
      Q s flux u g ξ hs0 hflux hu hg hξLp hBg hBavg hC havg hneg hpos hproj hneg1

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_note_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u g : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bavg Bcirc1 BcircS B C Bg : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hneg1 : ∀ N : ℕ, cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ Bcirc1)
    (hnegS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ BcircS)
    (hBg_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg := by
    intro N
    have hpartial :=
      cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_poincare_cutoff_terms
        Q s N u g ξ hB hu (hproj N) hg hξLp hξ hderiv hs0 hs1 hC
    have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
      exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
    have hterm1 :
        cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
          ≤
        cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) := by
      refine mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine mul_le_mul_of_nonneg_left (hneg1 N) ?_
      exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
    have hnoteS_nonneg :
        0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) := by
      have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _))
        (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
    have hterm2inner :
        cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)
          ≤
        cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
              BcircS) := by
      refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg (-s) Q)
      exact mul_le_mul_of_nonneg_left (hnegS N) hnoteS_nonneg
    have hterm2 :
        cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
                cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))
          ≤
        cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 - (3 : ℝ) ^ (-s))⁻¹) *
                BcircS)) := by
      exact mul_le_mul_of_nonneg_left hterm2inner (cubeLpNorm_nonneg Q ∞ ξ)
    calc
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x)
          ≤
        2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) *
                cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := hpartial
      _ ≤
        2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Bcirc1)) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) := by
              exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
      _ ≤ Bg := hBg_bound
  exact
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds_of_projectedDualMeanZeroPoincareEstimate
      Q s flux u g ξ hs0 hflux hu hg hξLp hBg hBavg hC havg hneg hpos hproj hneg1

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_note_terms_of_contDiff_component_vector_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bavg Bcirc1 BcircS B C Bg : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBg_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg := by
    intro N
    exact le_trans
      (cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_vector_poincare_cutoff_terms
        Q s N u G ξ hB hu (hproj N) hG hξLp hξ hderiv hs0 hs1 hC hBcircS
        (fun i => hGcirc1 i N) (fun i => hGcircS i N))
      hBg_bound
  exact
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_average_note_terms_of_partialBounds_of_projectedDualMeanZeroVectorPoincareEstimate
      Q s flux u G ξ hs0 hflux hu hG hξLp hBg hBavg hC havg hneg hpos hproj
      hGcirc1

theorem
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_note_terms_of_contDiff_component_vector_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d)
    {Bu Bavg Bcirc1 BcircS B C Bg : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg) (hC : 0 ≤ C) (hBcircS : 0 ≤ BcircS)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ Bcirc1)
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ BcircS)
    (hBg_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS)))) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x - cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (Bavg * (cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg))) := by
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => (u x - cubeAverage Q u) • ξ x) ≤ Bg := by
    intro N
    exact le_trans
      (cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_note_vector_poincare_cutoff_terms
        Q s N u G ξ hB hu (hproj N) hG hξLp hξ hderiv hs0 hs1 hC hBcircS
        (fun i => hGcirc1 i N) (fun i => hGcircS i N))
      hBg_bound
  exact
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds_of_projectedDualMeanZeroVectorPoincareEstimate
      Q s flux u G ξ hs0 hflux hu hG hξLp hBg hBavg hC havg hneg hpos hproj
      hGcirc1

end

end Homogenization
