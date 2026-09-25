/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct

/-! # Local Pairing -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem abs_cubeAverage_vecDot_scalar_smul_le_collapsed_average_note_terms_of_partialBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bg Bavg : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x • ξ x) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
  have hprod :
      MeasureTheory.MemLp (fun x => u x • ξ x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using! hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hu
  have hmain :=
    abs_cubeAverage_vecDot_le_sum_average_terms_add_note_terms_of_partialBounds
      Q s flux (fun x => u x • ξ x) hs hflux hprod hBg hneg hpos
  have hprod_bound :
      ‖cubeAverageVec Q (fun x => u x • ξ x)‖ ≤
        cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u :=
    norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two Q u ξ hu hξLp
  have hprod_bound_nonneg :
      0 ≤ cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)
  have hflux_comp :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => flux x i)‖ ≤ Bavg := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hBavg).mp havg i
  have hprod_comp :
      ∀ i : Fin d,
        ‖cubeAverage Q (fun x => (u x • ξ x) i)‖ ≤
          cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hprod_bound_nonneg).mp hprod_bound i
  have havg_term :
      ∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
          ‖cubeAverage Q (fun x => (u x • ξ x) i)‖
        ≤
      (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) := by
    calc
      ∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
          ‖cubeAverage Q (fun x => (u x • ξ x) i)‖
          ≤ ∑ i : Fin d, Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact mul_le_mul (hflux_comp i) (hprod_comp i) (norm_nonneg _) hBavg
      _ = (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) := by
            simp
  have hweight_nonneg : 0 ≤ cubeBesovScaleWeight s Q := cubeBesovScaleWeight_nonneg s Q
  have hnote_scale_nonneg : 0 ≤ cubeBesovScaleWeight s Q * Bg := by
    exact mul_nonneg hweight_nonneg hBg
  have hnote_term :
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => flux x i)‖) *
        (cubeBesovScaleWeight s Q * Bg))
        ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg))) := by
    calc
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => flux x i)‖) *
        (cubeBesovScaleWeight s Q * Bg))
          ≤
        ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * Bavg) *
          (cubeBesovScaleWeight s Q * Bg)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hinner :
                  (3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
                      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => flux x i)‖
                    ≤
                  (3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
                      cubeBesovScaleWeight s Q * Bavg := by
                exact add_le_add
                  le_rfl
                  (mul_le_mul_of_nonneg_left (hflux_comp i) hweight_nonneg)
              exact mul_le_mul_of_nonneg_right hinner hnote_scale_nonneg
      _ = (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * Bavg) *
            (cubeBesovScaleWeight s Q * Bg))) := by
            simp
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        ≤
      (∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
          ‖cubeAverage Q (fun x => (u x • ξ x) i)‖) +
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => flux x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := hmain
    _ ≤ (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu) +
              cubeBesovScaleWeight s Q * Bavg) *
              (cubeBesovScaleWeight s Q * Bg))) := by
            exact add_le_add havg_term hnote_term

/-- Sharp local pairing estimate.  This is the same average/fluctuation split
as `abs_cubeAverage_vecDot_scalar_smul_le_collapsed_average_note_terms_of_partialBounds`,
but the fluctuation piece uses the circ-only negative Besov duality bound, so
no positive-average tail is present in the Besov term. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_collapsed_sharp_average_note_terms_of_partialBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bg Bavg : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hpos : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x • ξ x) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
  have hprod :
      MeasureTheory.MemLp (fun x => u x • ξ x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using! hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hu
  have hmain :=
    abs_cubeAverage_vecDot_le_sum_average_terms_add_sharp_note_terms_of_partialBounds
      Q s flux (fun x => u x • ξ x) hs hflux hprod hBg hneg hpos
  have hprod_bound :
      ‖cubeAverageVec Q (fun x => u x • ξ x)‖ ≤
        cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u :=
    norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two Q u ξ hu hξLp
  have hprod_bound_nonneg :
      0 ≤ cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)
  have hflux_comp :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => flux x i)‖ ≤ Bavg := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hBavg).mp havg i
  have hprod_comp :
      ∀ i : Fin d,
        ‖cubeAverage Q (fun x => (u x • ξ x) i)‖ ≤
          cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hprod_bound_nonneg).mp hprod_bound i
  have havg_term :
      ∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
          ‖cubeAverage Q (fun x => (u x • ξ x) i)‖
        ≤
      (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) := by
    calc
      ∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
          ‖cubeAverage Q (fun x => (u x • ξ x) i)‖
          ≤ ∑ i : Fin d, Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact mul_le_mul (hflux_comp i) (hprod_comp i) (norm_nonneg _) hBavg
      _ = (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) := by
            simp
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        ≤
      (∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
          ‖cubeAverage Q (fun x => (u x • ξ x) i)‖) +
        (d : ℝ) *
          (((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg)) := hmain
    _ ≤ (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
              (cubeBesovScaleWeight s Q * Bg))) := by
            exact add_le_add havg_term le_rfl

/-- Sharp local pairing estimate with the positive cutoff-product control
stated directly as componentwise dual-test bounds. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_collapsed_sharp_average_note_terms_of_dualTestBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bg Bavg : ℝ}
    (hs : 0 < s)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤ Bu)
    (hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q (fun y => u y • ξ y) x i) ≤
          cubeBesovScaleWeight s Q * Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg))) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
  let prod : Vec d → Vec d := fun x => u x • ξ x
  have hprod :
      MeasureTheory.MemLp prod (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [prod] using! hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hu
  have hdecomp :
      cubeAverage Q (fun x => vecDot (flux x) (prod x)) =
        vecDot (cubeAverageVec Q flux) (cubeAverageVec Q prod) +
          cubeAverage Q (fun x => vecDot (flux x) (cubeFluctuationVec Q prod x)) :=
    cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
      Q flux prod hflux hprod
  have hfluct :
      |cubeAverage Q (fun x => vecDot (flux x) (cubeFluctuationVec Q prod x))| ≤
        (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
    exact
      abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_dualTestBounds
        Q s flux prod hs hflux hprod hBg hneg (by
          intro i N
          simpa [prod] using hdual i N)
  have hprod_bound :
      ‖cubeAverageVec Q prod‖ ≤
        cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    simpa [prod] using
      norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two Q u ξ hu hξLp
  have hprod_bound_nonneg :
      0 ≤ cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)
  have hflux_comp :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => flux x i)‖ ≤ Bavg := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hBavg).mp havg i
  have hprod_comp :
      ∀ i : Fin d,
        ‖cubeAverage Q (fun x => prod x i)‖ ≤
          cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hprod_bound_nonneg).mp hprod_bound i
  have havg_term :
      |vecDot (cubeAverageVec Q flux) (cubeAverageVec Q prod)| ≤
        (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) := by
    calc
      |vecDot (cubeAverageVec Q flux) (cubeAverageVec Q prod)|
          ≤ ∑ i, ‖cubeAverage Q (fun x => flux x i)‖ *
              ‖cubeAverage Q (fun x => prod x i)‖ := by
            exact abs_vecDot_cubeAverageVec_le_sum_norm_mul_norm Q flux prod
      _ ≤ ∑ i : Fin d, Bavg *
            (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul (hflux_comp i) (hprod_comp i) (norm_nonneg _) hBavg
      _ = (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) := by
            simp
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        = |cubeAverage Q (fun x => vecDot (flux x) (prod x))| := by rfl
    _ = |vecDot (cubeAverageVec Q flux) (cubeAverageVec Q prod) +
          cubeAverage Q (fun x => vecDot (flux x) (cubeFluctuationVec Q prod x))| := by
          rw [hdecomp]
    _ ≤ |vecDot (cubeAverageVec Q flux) (cubeAverageVec Q prod)| +
          |cubeAverage Q (fun x => vecDot (flux x) (cubeFluctuationVec Q prod x))| :=
          abs_add_le _ _
    _ ≤ (d : ℝ) * (Bavg * (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u)) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * Bu)) *
              (cubeBesovScaleWeight s Q * Bg))) := by
            exact add_le_add havg_term hfluct

theorem abs_cubeAverage_vecDot_const_scalar_smul_le_collapsed_note_terms_of_componentDualBounds
    {d : ℕ} (Q : TriadicCube d) (flux ξ : Vec d → Vec d) (c : ℝ) {Bu Bg Bavg : ℝ}
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu)
    (hnorm : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => c * ξ x i) ≤ Bg)
    (hmem : ∀ i : Fin d,
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => c * ξ x i)) :
    |cubeAverage Q (fun x => vecDot (flux x) (c • ξ x))| ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) +
          cubeBesovScaleWeight 1 Q * Bavg) * Bg)) := by
  have hflux_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => flux x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp flux i hflux
  have hmain :=
    abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_one_of_nonneg
      Q 1 flux (fun x => c • ξ x) (fun _ => Bg) (by norm_num) hflux_comp (fun _ => hBg)
      (by
        intro i N
        simpa [Pi.smul_apply, smul_eq_mul] using hnorm i N)
      (by
        intro i
        simpa [Pi.smul_apply, smul_eq_mul] using hmem i)
  have hflux_comp_avg :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => flux x i)‖ ≤ Bavg := by
    intro i
    simpa [cubeAverageVec] using
      (pi_norm_le_iff_of_nonneg hBavg).mp havg i
  have hBg_nonneg : 0 ≤ Bg := hBg
  have hweight_nonneg : 0 ≤ cubeBesovScaleWeight 1 Q := cubeBesovScaleWeight_nonneg 1 Q
  have hnote_term :
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) +
        cubeBesovScaleWeight 1 Q * ‖cubeAverage Q (fun x => flux x i)‖) * Bg)
        ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) +
          cubeBesovScaleWeight 1 Q * Bavg) * Bg)) := by
    calc
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) +
        cubeBesovScaleWeight 1 Q * ‖cubeAverage Q (fun x => flux x i)‖) * Bg)
          ≤
        ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + 1) *
            (cubeBesovScaleWeight (-1) Q * Bu) +
          cubeBesovScaleWeight 1 Q * Bavg) * Bg) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hcomponent :
                cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) ≤
                  cubeBesovScaleWeight (-1) Q * Bu := by
              exact
                cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
                  Q 1 flux i hneg
            have hinner :
                (3 : ℝ) ^ ((d : ℝ) + 1) *
                    cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) +
                  cubeBesovScaleWeight 1 Q * ‖cubeAverage Q (fun x => flux x i)‖
                  ≤
                (3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) +
                  cubeBesovScaleWeight 1 Q * Bavg := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hcomponent
                  (Real.rpow_nonneg (by positivity : 0 ≤ (3 : ℝ)) _))
                (mul_le_mul_of_nonneg_left (hflux_comp_avg i) hweight_nonneg)
            exact mul_le_mul_of_nonneg_right hinner hBg_nonneg
      _ = (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) +
            cubeBesovScaleWeight 1 Q * Bavg) * Bg)) := by
            simp
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (c • ξ x))|
        ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) +
        cubeBesovScaleWeight 1 Q * ‖cubeAverage Q (fun x => flux x i)‖) * Bg) := by
            simpa using hmain
    _ ≤ (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) +
            cubeBesovScaleWeight 1 Q * Bavg) * Bg)) := hnote_term

/-- Sharp constant-piece pairing estimate.  This is the LaTeX
`[a∇u]_{B^{-1}}` line: the full negative Besov dual norm is controlled by the
negative circ norm alone, so the flux side contributes only the
`cubeBesovScaleWeight (-1)` factor. -/
theorem abs_cubeAverage_vecDot_const_scalar_smul_le_collapsed_sharp_note_terms_of_componentDualBounds
    {d : ℕ} (Q : TriadicCube d) (flux ξ : Vec d → Vec d) (c : ℝ) {Bu Bg : ℝ}
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu)
    (hnorm : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => c * ξ x i) ≤ Bg)
    (hmem : ∀ i : Fin d,
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => c * ξ x i)) :
    |cubeAverage Q (fun x => vecDot (flux x) (c • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu)) *
          Bg) := by
  have hflux_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => flux x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp flux i hflux
  have hmain :=
    abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_one_of_nonneg
      Q 1 flux (fun x => c • ξ x) (fun _ => Bg) (by norm_num) hflux_comp
      (fun _ => hBg)
      (by
        intro i N
        simpa [Pi.smul_apply, smul_eq_mul] using hnorm i N)
      (by
        intro i
        simpa [Pi.smul_apply, smul_eq_mul] using hmem i)
  have hBg_nonneg : 0 ≤ Bg := hBg
  have hnote_term :
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i)) *
        Bg)
        ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu)) *
          Bg) := by
    calc
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i)) *
        Bg)
          ≤
        ∑ i : Fin d,
          (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu)) *
            Bg) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hcomponent :
                cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i) ≤
                  cubeBesovScaleWeight (-1) Q * Bu := by
              exact
                cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
                  Q 1 flux i hneg
            have hinner :
                (3 : ℝ) ^ ((d : ℝ) + 1) *
                    cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => flux x i)
                  ≤
                (3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) := by
              exact mul_le_mul_of_nonneg_left hcomponent
                (Real.rpow_nonneg (by positivity : 0 ≤ (3 : ℝ)) _)
            exact mul_le_mul_of_nonneg_right hinner hBg_nonneg
      _ = (d : ℝ) *
          (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu)) *
            Bg) := by
            simp
  exact le_trans hmain hnote_term

theorem abs_cubeAverage_vecDot_cubeAverage_scalar_smul_le_collapsed_note_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu Bavg B Bg : ℝ}
    (hB : 0 ≤ B)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg) (hBavg : 0 ≤ Bavg)
    (havg : ‖cubeAverageVec Q flux‖ ≤ Bavg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hBg_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu) +
          cubeBesovScaleWeight 1 Q * Bavg) * Bg)) := by
  have hξScaled_infty :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) ∞ (normalizedCubeMeasure Q) := by
    simpa [Pi.smul_apply] using! hξLp.const_smul (cubeAverage Q u)
  have hξScaled_two :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hξScaled_infty.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
          (fun x => cubeAverage Q u * ξ x i) := by
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using
      cubeBesovDualLocalMemLpGlobal_component_of_memLp
        Q (fun x => (cubeAverage Q u) • ξ x) i hξScaled_two
  have huavg :
      ‖cubeAverage Q u‖ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u :=
    norm_cubeAverage_le_cubeLpNorm_two Q u hu
  have hcoeff_nonneg : 0 ≤ B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ := by
    exact add_nonneg hB
      (mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) (cubeLpNorm_nonneg Q ∞ ξ))
  have hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeAverage Q u * ξ x i) ≤ Bg := by
    intro i N
    calc
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeAverage Q u * ξ x i)
          ≤ ‖cubeAverage Q u‖ *
              cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => ξ x i) := by
                simpa [smul_eq_mul] using
                  cubeBesovDualTestNorm_two_one_const_mul_le
                    Q 1 N (cubeAverage Q u) (fun x => ξ x i)
      _ ≤ ‖cubeAverage Q u‖ * (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) := by
            exact mul_le_mul_of_nonneg_left
              (cubeBesovDualTestNorm_one_two_component_le_of_contDiff_component_bound
                Q ξ i N hB hξLp hξ hderiv)
              (norm_nonneg _)
      _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u * (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) := by
            exact mul_le_mul_of_nonneg_right huavg hcoeff_nonneg
      _ ≤ Bg := hBg_bound
  simpa using
    abs_cubeAverage_vecDot_const_scalar_smul_le_collapsed_note_terms_of_componentDualBounds
      Q flux ξ (cubeAverage Q u) hflux hBg hBavg havg hneg hnorm hmem

/-- Sharp constant-piece estimate after bounding the cutoff dual-test norm by
the quantitative derivative bound.  This is the direct Lean counterpart of
the LaTeX bound
`C 3^k Λ_1(R)^{1/2} |u_R| E_R`, before the local mean is bounded by the
local `L²` norm. -/
theorem abs_cubeAverage_vecDot_cubeAverage_scalar_smul_le_collapsed_sharp_note_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (flux : Vec d → Vec d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {Bu B Bg : ℝ}
    (hB : 0 ≤ B)
    (hflux : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q 1 N flux ≤ Bu)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hBg_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (flux x) ((cubeAverage Q u) • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Bu)) *
          Bg) := by
  have hξScaled_infty :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) ∞ (normalizedCubeMeasure Q) := by
    simpa [Pi.smul_apply] using! hξLp.const_smul (cubeAverage Q u)
  have hξScaled_two :
      MeasureTheory.MemLp (fun x => (cubeAverage Q u) • ξ x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hξScaled_infty.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
          (fun x => cubeAverage Q u * ξ x i) := by
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using
      cubeBesovDualLocalMemLpGlobal_component_of_memLp
        Q (fun x => (cubeAverage Q u) • ξ x) i hξScaled_two
  have huavg :
      ‖cubeAverage Q u‖ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u :=
    norm_cubeAverage_le_cubeLpNorm_two Q u hu
  have hcoeff_nonneg : 0 ≤ B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ := by
    exact add_nonneg hB
      (mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) (cubeLpNorm_nonneg Q ∞ ξ))
  have hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeAverage Q u * ξ x i) ≤ Bg := by
    intro i N
    calc
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeAverage Q u * ξ x i)
          ≤ ‖cubeAverage Q u‖ *
              cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => ξ x i) := by
                simpa [smul_eq_mul] using
                  cubeBesovDualTestNorm_two_one_const_mul_le
                    Q 1 N (cubeAverage Q u) (fun x => ξ x i)
      _ ≤ ‖cubeAverage Q u‖ * (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) := by
            exact mul_le_mul_of_nonneg_left
              (cubeBesovDualTestNorm_one_two_component_le_of_contDiff_component_bound
                Q ξ i N hB hξLp hξ hderiv)
              (norm_nonneg _)
      _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u * (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) := by
            exact mul_le_mul_of_nonneg_right huavg hcoeff_nonneg
      _ ≤ Bg := hBg_bound
  simpa using
    abs_cubeAverage_vecDot_const_scalar_smul_le_collapsed_sharp_note_terms_of_componentDualBounds
      Q flux ξ (cubeAverage Q u) hflux hBg hneg hnorm hmem

theorem cubeLpNorm_two_le_note_rhs_of_meanZero_projectedDualMeanZeroPoincareEstimate
    {d : ℕ} (Q : TriadicCube d) (N : ℕ) (v g : Vec d → ℝ) {C : ℝ}
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C v g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (havg : cubeAverage Q v = 0) (hC : 0 ≤ C) :
    cubeLpNorm Q (2 : ℝ≥0∞) v ≤
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g := by
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) v
        ≤ cubeBesovPartialNormTop Q 0 (2 : ℝ≥0∞) 0 v :=
          cubeLpNorm_two_le_cubeBesovPartialNormTop_zero Q v hv
    _ ≤ cubeBesovPartialNormTop Q 0 (2 : ℝ≥0∞) N v :=
          cubeBesovPartialNormTop_zero_le Q 0 (2 : ℝ≥0∞) N v
    _ ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g := by
            simpa using
              hproj.partialNormTop_two_le_cubeBesovCircPartialNorm (s := 0) hg havg
                (by norm_num) hC


end

end Homogenization
