/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliBridge
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliVectorization
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapBridge

/-! # Overlap Caccioppoli Bridge -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-!
# Overlap dual tests in the Caccioppoli pairing bridge

These wrappers route uniform overlap dual-test norm bounds through the
finite-depth norm switch and then reuse the existing circ-domination estimates.
The test-function local `MemLp` input is kept as the existing global disjoint
admissibility predicate; it is not inferred from the overlap local predicate.
-/

private theorem cubeBesovConjExponent_two_eq_overlapBridge :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

private theorem cubeBesovConjExponent_two_ne_top_overlapBridge :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [cubeBesovConjExponent_two_eq_overlapBridge]
  norm_num

theorem abs_cubeBesovPairing_le_note_constant_mul_of_overlap_uniform_bound_two_one_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B) := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2)
  have hC_nonneg : 0 ≤ C :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hnorm_disjoint :
      ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ C * B := by
    intro N
    have hbridge :=
      cubeBesovDualTestNorm_le_three_rpow_mul_overlapDualTestNorm
        (Q := Q) (s := s) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞))
        (N := N) (g := g) cubeBesovConjExponent_two_ne_top_overlapBridge
        (by norm_num)
    have hbridgeC :
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g
          ≤ C * cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g := by
      simpa [C, cubeBesovConjExponent_two_eq_overlapBridge] using hbridge
    exact hbridgeC.trans (mul_le_mul_of_nonneg_left (hnorm N) hC_nonneg)
  have hCB_nonneg : 0 ≤ C * B := mul_nonneg hC_nonneg hB
  simpa [C] using
    abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
      Q s u g hs hu hCB_nonneg hnorm_disjoint hmem

theorem abs_cubeBesovPairing_le_note_rhs_mul_of_overlap_uniform_bound_two_two_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B) := by
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2)
  have hC_nonneg : 0 ≤ C :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hnorm_disjoint :
      ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ C * B := by
    intro N
    have hbridge :=
      cubeBesovDualTestNorm_le_three_rpow_mul_overlapDualTestNorm
        (Q := Q) (s := s) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (N := N) (g := g) cubeBesovConjExponent_two_ne_top_overlapBridge
        (by norm_num)
    have hbridgeC :
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g
          ≤ C * cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g := by
      simpa [C, cubeBesovConjExponent_two_eq_overlapBridge] using hbridge
    exact hbridgeC.trans (mul_le_mul_of_nonneg_left (hnorm N) hC_nonneg)
  have hCB_nonneg : 0 ≤ C * B := mul_nonneg hC_nonneg hB
  simpa [C] using
    abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two_of_nonneg
      Q s u g hs hu hCB_nonneg hnorm_disjoint hmem

theorem abs_cubeBesovPairing_le_note_constant_mul_of_overlap_uniform_bound_two_one_of_memLp_parent
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B) := by
  have hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g :=
    CubeBesovDualLocalMemLpGlobal.of_memLp_parent
      (by simpa [cubeBesovConjExponent_two_eq_overlapBridge] using hg)
  exact
    abs_cubeBesovPairing_le_note_constant_mul_of_overlap_uniform_bound_two_one_of_nonneg
      Q s u g hs hu hB hnorm hmem

theorem abs_cubeBesovPairing_le_note_rhs_mul_of_overlap_uniform_bound_two_two_of_memLp_parent
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B) := by
  have hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g :=
    CubeBesovDualLocalMemLpGlobal.of_memLp_parent
      (by simpa [cubeBesovConjExponent_two_eq_overlapBridge] using hg)
  exact
    abs_cubeBesovPairing_le_note_rhs_mul_of_overlap_uniform_bound_two_two_of_nonneg
      Q s u g hs hu hB hnorm hmem

theorem abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_overlap_uniform_component_bounds_two_one_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B i)) := by
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa [cubeBesovConjExponent_two_eq_overlapBridge] using
        (hmem i).memLp
    simpa [Pi.mul_apply, mul_comm] using! (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B i)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact
            abs_cubeBesovPairing_le_note_constant_mul_of_overlap_uniform_bound_two_one_of_nonneg
              Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i)
              (hnorm i) (hmem i)

theorem abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_overlap_uniform_component_bounds_two_one_of_memLp_parent
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : ∀ i, MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => g x i) ≤ B i) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B i)) := by
  have hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i) := by
    intro i
    exact CubeBesovDualLocalMemLpGlobal.of_memLp_parent
      (by simpa [cubeBesovConjExponent_two_eq_overlapBridge] using hg i)
  exact
    abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_overlap_uniform_component_bounds_two_one_of_nonneg
      Q s u g B hs hu hB hnorm hmem

theorem abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_overlap_uniform_component_bounds_two_two_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B i)) := by
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa [cubeBesovConjExponent_two_eq_overlapBridge] using
        (hmem i).memLp
    simpa [Pi.mul_apply, mul_comm] using! (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B i)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact
            abs_cubeBesovPairing_le_note_rhs_mul_of_overlap_uniform_bound_two_two_of_nonneg
              Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i)
              (hnorm i) (hmem i)

theorem abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_overlap_uniform_component_bounds_two_two_of_memLp_parent
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : ∀ i, MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovOverlapDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => g x i) ≤ B i) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        ((3 : ℝ) ^ ((d : ℝ) / 2) * B i)) := by
  have hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i) := by
    intro i
    exact CubeBesovDualLocalMemLpGlobal.of_memLp_parent
      (by simpa [cubeBesovConjExponent_two_eq_overlapBridge] using hg i)
  exact
    abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_overlap_uniform_component_bounds_two_two_of_nonneg
      Q s u g B hs hu hB hnorm hmem

end Homogenization
