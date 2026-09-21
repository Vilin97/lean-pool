/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise

/-! # Coarse Caccioppoli Local Bridge -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
    {d : ℕ} (Q : TriadicCube d) (u g : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecDot (u x) (g x)) =
      vecDot (cubeAverageVec Q u) (cubeAverageVec Q g) +
        cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x)) := by
  have hu_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp u i hu
  have hg_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp g i hg
  have hgFluct :
      MeasureTheory.MemLp (cubeFluctuationVec Q g) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q g hg
  have hgFluct_comp :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => cubeFluctuationVec Q g x i)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp (cubeFluctuationVec Q g) i hgFluct
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    simpa [Pi.mul_apply, mul_comm] using! (hu_comp i).integrable_mul (hg_comp i)
  have hIntFluct :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * cubeFluctuationVec Q g x i)
          (normalizedCubeMeasure Q) := by
    intro i
    simpa [Pi.mul_apply, mul_comm] using! (hu_comp i).integrable_mul (hgFluct_comp i)
  calc
    cubeAverage Q (fun x => vecDot (u x) (g x))
        = ∑ i, cubeBesovPairing Q (fun x => u x i) (fun x => g x i) := by
            exact cubeAverage_vecDot_eq_sum_cubeBesovPairing Q u g hInt
    _ = ∑ i, (cubeAverage Q (fun x => u x i) * cubeAverage Q (fun x => g x i) +
          cubeBesovPairing Q (fun x => u x i)
            (fun x => cubeFluctuationVec Q g x i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            cubeBesovPairing Q (fun x => u x i) (fun x => g x i)
                = cubeBesovPairing Q (fun x => u x i)
                    (fun x => cubeAverage Q (fun y => g y i) + cubeFluctuationVec Q g x i) := by
                      congr 1
                      funext x
                      simp [cubeFluctuationVec, cubeAverageVec]
            _ = cubeAverage Q (fun x => u x i * cubeAverage Q (fun y => g y i)) +
                  cubeBesovPairing Q (fun x => u x i)
                    (fun x => cubeFluctuationVec Q g x i) := by
                  have hsplit :
                      (fun x => u x i *
                          (cubeAverage Q (fun y => g y i) + cubeFluctuationVec Q g x i)) =
                        (fun x => u x i * cubeAverage Q (fun y => g y i) +
                          u x i * cubeFluctuationVec Q g x i) := by
                            funext x
                            ring
                  have hIntConst :
                      MeasureTheory.Integrable
                        (fun x => u x i * cubeAverage Q (fun y => g y i))
                        (normalizedCubeMeasure Q) := by
                          have huInt :
                              MeasureTheory.Integrable (fun x => u x i)
                                (normalizedCubeMeasure Q) :=
                            (hu_comp i).integrable (by norm_num)
                          have hIntConst' :
                              MeasureTheory.Integrable
                                (fun x => cubeAverage Q (fun y => g y i) * u x i)
                                (normalizedCubeMeasure Q) :=
                            huInt.const_mul (cubeAverage Q (fun y => g y i))
                          simpa [mul_comm] using hIntConst'
                  unfold cubeBesovPairing
                  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
                  rw [hsplit]
                  rw [MeasureTheory.integral_add hIntConst (hIntFluct i)]
                  rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q
                    (fun x => u x i * cubeAverage Q (fun y => g y i))]
                  rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q
                    (fun x => u x i * cubeFluctuationVec Q g x i)]
            _ = cubeAverage Q (fun x => u x i) * cubeAverage Q (fun x => g x i) +
                  cubeBesovPairing Q (fun x => u x i)
                    (fun x => cubeFluctuationVec Q g x i) := by
                  have hconst :
                      (fun x => u x i * cubeAverage Q (fun y => g y i)) =
                        fun x => cubeAverage Q (fun y => g y i) * u x i := by
                          funext x
                          ring
                  rw [hconst, cubeAverage_const_mul]
                  ring
    _ = (∑ i, cubeAverage Q (fun x => u x i) * cubeAverage Q (fun x => g x i)) +
          ∑ i, cubeBesovPairing Q (fun x => u x i)
            (fun x => cubeFluctuationVec Q g x i) := by
          rw [Finset.sum_add_distrib]
    _ = vecDot (cubeAverageVec Q u) (cubeAverageVec Q g) +
          cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x)) := by
          rw [cubeAverage_vecDot_eq_sum_cubeBesovPairing Q u (cubeFluctuationVec Q g) hIntFluct]
          simp [vecDot, cubeAverageVec]

theorem abs_vecDot_cubeAverageVec_le_sum_norm_mul_norm {d : ℕ}
    (Q : TriadicCube d) (u g : Vec d → Vec d) :
    |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g)| ≤
      ∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖ := by
  calc
    |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g)|
        = |∑ i, cubeAverage Q (fun x => u x i) * cubeAverage Q (fun x => g x i)| := by
            simp [vecDot, cubeAverageVec]
    _ ≤ ∑ i, |cubeAverage Q (fun x => u x i) * cubeAverage Q (fun x => g x i)| := by
          exact Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun i : Fin d => cubeAverage Q (fun x => u x i) * cubeAverage Q (fun x => g x i))
    _ = ∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]

theorem abs_cubeAverage_vecDot_le_sum_average_terms_add_note_terms_of_partialBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
  have hdecomp :=
    cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
      Q u g hu hg
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        = |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g) +
            cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
              rw [hdecomp]
    _ ≤ |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g)| +
          |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            exact abs_add_le _ _
    _ ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
          |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            exact add_le_add
              (abs_vecDot_cubeAverageVec_le_sum_norm_mul_norm Q u g) le_rfl
    _ ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
          ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
              (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
            (cubeBesovScaleWeight s Q * Bg)) := by
          exact add_le_add le_rfl
            (abs_cubeAverage_vecDot_fluctuationVec_le_sum_note_terms_of_partialBounds
              Q s u g hs hu hg hBg hneg hpos)

/-- Sharp average/fluctuation split for the vector product.  Compared with
`abs_cubeAverage_vecDot_le_sum_average_terms_add_note_terms_of_partialBounds`,
the fluctuation piece uses the sharp Besov duality bound and therefore does
not carry the extra positive average tail on the flux side. -/
theorem abs_cubeAverage_vecDot_le_sum_average_terms_add_sharp_note_terms_of_partialBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
        (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
  have hdecomp :=
    cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
      Q u g hu hg
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        = |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g) +
            cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
              rw [hdecomp]
    _ ≤ |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g)| +
          |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            exact abs_add_le _ _
    _ ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
          |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            exact add_le_add
              (abs_vecDot_cubeAverageVec_le_sum_norm_mul_norm Q u g) le_rfl
    _ ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
          (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu)) *
            (cubeBesovScaleWeight s Q * Bg)) := by
          exact add_le_add le_rfl
            (abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds
              Q s u g hs hu hg hBg hneg hpos)

theorem abs_cubeAverage_vecDot_le_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (havg : cubeAverageVec Q g = 0)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hmain :=
    abs_cubeAverage_vecDot_le_sum_average_terms_add_note_terms_of_partialBounds
      Q s u g hs hu hg hBg hneg hpos
  have hmean_zero :
      ∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hgi : cubeAverage Q (fun x => g x i) = 0 := by
      simpa [cubeAverageVec] using congrFun havg i
    rw [hgi]
    simp
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
            ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
                (cubeBesovScaleWeight (-s) Q * Bu) +
              cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
              (cubeBesovScaleWeight s Q * Bg)) := hmain
    _ = ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
          rw [hmean_zero, zero_add]

theorem abs_cubeAverage_vecDot_le_sum_average_terms_add_note_terms_of_partialBounds_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
        ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
  have hdecomp :=
    cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
      Q u g hu hg
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        = |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g) +
            cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
              rw [hdecomp]
    _ ≤ |vecDot (cubeAverageVec Q u) (cubeAverageVec Q g)| +
          |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            exact abs_add_le _ _
    _ ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
          |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            exact add_le_add
              (abs_vecDot_cubeAverageVec_le_sum_norm_mul_norm Q u g) le_rfl
    _ ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
          ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
              (cubeBesovScaleWeight (-s) Q * Bu) +
            cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
            (cubeBesovScaleWeight s Q * Bg)) := by
          exact add_le_add le_rfl
            (abs_cubeAverage_vecDot_fluctuationVec_le_sum_note_terms_of_partialBounds_two_two
              Q s u g hs hu hg hBg hneg hpos)

theorem abs_cubeAverage_vecDot_le_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (havg : cubeAverageVec Q g = 0)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hmain :=
    abs_cubeAverage_vecDot_le_sum_average_terms_add_note_terms_of_partialBounds_two_two
      Q s u g hs hu hg hBg hneg hpos
  have hmean_zero :
      ∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hgi : cubeAverage Q (fun x => g x i) = 0 := by
      simpa [cubeAverageVec] using congrFun havg i
    rw [hgi]
    simp
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ (∑ i, ‖cubeAverage Q (fun x => u x i)‖ * ‖cubeAverage Q (fun x => g x i)‖) +
            ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
                (cubeBesovScaleWeight (-s) Q * Bu) +
              cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
              (cubeBesovScaleWeight s Q * Bg)) := hmain
    _ = ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * Bu) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
          rw [hmean_zero, zero_add]

/-- Sharp centered `q = 2` vector pairing bound.  The depth-zero negative
seminorm absorbs the average contribution, so no separate average tail remains
when the second field has zero cube average. -/
theorem abs_cubeAverage_vecDot_le_sharp_note_terms_of_partialBounds_of_cubeAverageVec_eq_zero_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (havg : cubeAverageVec Q g = 0)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hdecomp :=
    cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
      Q u g hu hg
  have hmean_zero :
      vecDot (cubeAverageVec Q u) (cubeAverageVec Q g) = 0 := by
    simp [havg, vecDot_zero_right]
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        = |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| := by
            rw [hdecomp, hmean_zero, zero_add]
    _ ≤ (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) :=
          abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two
            Q s u g hs hu hg hBg hneg hpos

end

end Homogenization
