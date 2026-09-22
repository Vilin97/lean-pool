/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesPositiveQTwo
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliBridge
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliVectorization
import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Bounds

/-! # Weak Norm Interfaces Componentwise -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_two {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hnorm : ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u) * B := by
  have hpConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [show cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))]
    norm_num
  have hpair :=
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two
      Q s u g hs hu hB hnorm hmem
  have hfull :=
    cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u hs hu (by norm_num) (by norm_num) hpConjTop
      (by norm_num)
  calc
    |cubeBesovPairing Q u g|
        ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u * B := hpair
    _ ≤
        ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u) * B := by
            exact mul_le_mul_of_nonneg_right hfull hB.le

theorem abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_two_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u) * B := by
  let A : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + s) *
      cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u
  have hCircBdd :
      BddAbove (cubeBesovCircNormValueSet Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u) :=
    cubeBesovCircNormValueSet_bddAbove_of_memLp Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u
      hs hu (by norm_num) (by norm_num) (by norm_num)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (cubeBesovCircNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u hCircBdd)
  change |cubeBesovPairing Q u g| ≤ A * B
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  have hBδ_pos : 0 < B + δ := add_pos_of_nonneg_of_pos hB hδ_pos
  have hnormδ :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B + δ := by
    intro N
    exact (hnorm N).trans (le_add_of_nonneg_right hδ_pos.le)
  have hstrict :=
    abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_two
      Q s u g hs hu hBδ_pos hnormδ hmem
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    |cubeBesovPairing Q u g| ≤ A * (B + δ) := by
      simpa [A] using hstrict
    _ = A * B + A * δ := by ring
    _ ≤ A * B + ε := by linarith

theorem abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_two_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i)) * B i) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hBi_pos : 0 < B i + 1 := add_pos_of_nonneg_of_pos (hB i) zero_lt_one
    have hnormBi :
        ∀ N : ℕ,
          cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
              (fun x => g x i) ≤
            B i + 1 := by
      intro N
      exact (hnorm i N).trans (le_add_of_nonneg_right zero_le_one)
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x => (B i + 1)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_two_of_uniform_bound Q s (fun x => g x i)
        hBi_pos hnormBi (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem :
          MeasureTheory.MemLp (fun x => (B i + 1)⁻¹ * g x i)
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst :
          MeasureTheory.MemLp (fun x => (B i + 1) * ((B i + 1)⁻¹ * g x i))
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [Pi.smul_apply, smul_eq_mul] using! hscaled_mem.const_smul (B i + 1)
      convert hconst using 1
      funext x
      field_simp [hBi_pos.ne']
    simpa [Pi.mul_apply, mul_comm] using! (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i)) * B i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_two_of_nonneg
            Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

theorem memLp_on_descendant_of_memLp_generic {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {Q R : TriadicCube d} {j : ℕ}
    {p : ℝ≥0∞} {f : Vec d → E}
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (normalizedCubeMeasure R) := by
  have hrestrict :
      MeasureTheory.MemLp f p ((normalizedCubeMeasure Q).restrict (cubeSet R)) :=
    hf.restrict (cubeSet R)
  have hle :
      normalizedCubeMeasure R ≤
        ENNReal.ofReal (cubeVolume Q / cubeVolume R) •
          (normalizedCubeMeasure Q).restrict (cubeSet R) := by
    simp [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
  exact hrestrict.of_measure_le_smul ENNReal.ofReal_ne_top hle

theorem memLp_component_of_memLp {d : ℕ} {Q : TriadicCube d}
    (u : Vec d → Vec d) (i : Fin d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu

theorem memLp_cubeFluctuationVec {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (cubeFluctuationVec Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverageVec Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (cubeAverageVec Q u)
  simpa [cubeFluctuationVec] using! hu.sub hconst

theorem cubeFluctuation_component_eq_cubeFluctuationVec_component {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (i : Fin d) :
    cubeFluctuation Q (fun x => u x i) = fun x => cubeFluctuationVec Q u x i := by
  funext x
  simp [cubeFluctuation, cubeFluctuationVec, cubeAverageVec]

theorem sqrt_sum_sq_const_mul_eq_componentwise {ι : Type*} (s : Finset ι) (c : ℝ) (F : ι → ℝ)
    (hc : 0 ≤ c) :
    Real.sqrt (Finset.sum s (fun i => (c * F i) ^ 2)) =
      c * Real.sqrt (Finset.sum s (fun i => (F i) ^ 2)) := by
  have hF_nonneg : 0 ≤ Finset.sum s (fun i => (F i) ^ 2) := by
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  calc
    Real.sqrt (Finset.sum s (fun i => (c * F i) ^ 2))
        = Real.sqrt (c ^ 2 * Finset.sum s (fun i => (F i) ^ 2)) := by
            congr 1
            calc
              Finset.sum s (fun i => (c * F i) ^ 2) = Finset.sum s (fun i => c ^ 2 * (F i) ^ 2) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
              _ = c ^ 2 * Finset.sum s (fun i => (F i) ^ 2) := by
                    rw [← Finset.mul_sum]
    _ = Real.sqrt (c ^ 2) * Real.sqrt (Finset.sum s (fun i => (F i) ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg c)]
    _ = c * Real.sqrt (Finset.sum s (fun i => (F i) ^ 2)) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

theorem cubeBesovNegativeVectorDepthSeminorm_le_partialSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (N j : ℕ)
    (hj : j ∈ Finset.range (N + 1)) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j ≤
      cubeBesovNegativeVectorPartialSeminorm Q s N u := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  exact Finset.single_le_sum
    (fun k _ => cubeBesovNegativeVectorDepthSeminorm_nonneg Q s u k) hj

theorem cubeBesovPositiveVectorDepthSeminorm_le_partialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (N j : ℕ)
    (hj : j ∈ Finset.range (N + 1)) :
    cubeBesovPositiveVectorDepthSeminorm Q s u j ≤
      cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  have hsq :
      (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ (2 : ℕ) ≤
        (cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ (2 : ℕ) := by
    rw [sq_cubeBesovPositiveVectorPartialSeminormTwo]
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (cubeBesovPositiveVectorDepthSeminorm Q s u k)) hj
  have hdepth_nonneg : 0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s u j :=
    cubeBesovPositiveVectorDepthSeminorm_nonneg Q s u j
  have hpartial_nonneg : 0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s N u :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s N u
  nlinarith

theorem cubeBesovCircDepthAverage_two_component_le_negativeVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (i : Fin d) (j : ℕ) :
    cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j ≤
      cubeBesovNegativeVectorDepthAverage Q u j := by
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R hR
  have hcoord :
      (cubeAverage R (fun x => u x i)) ^ (2 : ℕ) ≤ vecNormSq (cubeAverageVec R u) := by
    simpa [cubeAverageVec] using sq_apply_le_vecNormSq (cubeAverageVec R u) i
  simpa [cubeBesovNegativeVectorDepthAverage, cubeBesovCircDepthAverage,
    Real.rpow_natCast, pow_two, Real.norm_eq_abs] using hcoord

theorem cubeBesovCircDepthSeminorm_two_component_le_scaleWeight_neg_mul_negativeVectorDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (j : ℕ) :
    cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j ≤
      cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorDepthSeminorm Q s u j := by
  have havg :
      cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j ≤
        cubeBesovNegativeVectorDepthAverage Q u j :=
    cubeBesovCircDepthAverage_two_component_le_negativeVectorDepthAverage Q u i j
  have hsqrt :
      Real.sqrt (cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j) ≤
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j) := by
    exact Real.sqrt_le_sqrt havg
  have hweight :
      cubeBesovCircDepthWeight Q s j =
        cubeBesovScaleWeight (-s) Q * Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
    calc
      cubeBesovCircDepthWeight Q s j
          = cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s)) ^ j := by
              exact cubeBesovCircDepthWeight_eq_scaleWeight_neg_mul_geom Q s j
      _ = cubeBesovScaleWeight (-s) Q * Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
            congr 1
            calc
              ((3 : ℝ) ^ (-s)) ^ j = Real.rpow ((3 : ℝ) ^ (-s)) (j : ℝ) := by
                symm
                exact Real.rpow_natCast _ j
              _ = Real.rpow (3 : ℝ) ((-s) * (j : ℝ)) := by
                    simpa using
                      (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s) (j : ℝ)).symm
              _ = Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by ring
  have hweight_nonneg : 0 ≤ cubeBesovCircDepthWeight Q s j :=
    cubeBesovCircDepthWeight_nonneg Q s j
  calc
    cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j
        = cubeBesovCircDepthWeight Q s j *
            Real.sqrt (cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j) := by
              simp [cubeBesovCircDepthSeminorm, Real.sqrt_eq_rpow]
    _ ≤ cubeBesovCircDepthWeight Q s j *
          Real.sqrt (cubeBesovNegativeVectorDepthAverage Q u j) := by
            exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ = cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorDepthSeminorm Q s u j := by
          rw [hweight]
          simp [cubeBesovNegativeVectorDepthSeminorm, mul_assoc]

theorem cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => u x i) ≤
      cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorPartialSeminorm Q s N u := by
  calc
    cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => u x i)
        = Finset.sum (Finset.range (N + 1))
            (fun j => cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j) := by
              simp [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]
    _ ≤ Finset.sum (Finset.range (N + 1))
          (fun j =>
            cubeBesovScaleWeight (-s) Q *
              cubeBesovNegativeVectorDepthSeminorm Q s u j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact
              cubeBesovCircDepthSeminorm_two_component_le_scaleWeight_neg_mul_negativeVectorDepthSeminorm
                Q s u i j
    _ = cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorPartialSeminorm Q s N u := by
          simp [cubeBesovNegativeVectorPartialSeminorm, Finset.mul_sum]

theorem cubeBesovCircPartialNorm_two_two_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => u x i) ≤
      cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorPartialSeminormTwo Q s N u := by
  have hsum_le :
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j) ^ 2)
        ≤
      Finset.sum (Finset.range (N + 1))
          (fun j =>
            (cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hdepth :=
      cubeBesovCircDepthSeminorm_two_component_le_scaleWeight_neg_mul_negativeVectorDepthSeminorm
        Q s u i j
    have hleft_nonneg :
        0 ≤ cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j :=
      cubeBesovCircDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) (fun x => u x i) j
    have hright_nonneg :
        0 ≤ cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorDepthSeminorm Q s u j := by
      exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q)
        (cubeBesovNegativeVectorDepthSeminorm_nonneg Q s u j)
    nlinarith
  have hsum_nonneg :
      0 ≤ Finset.sum (Finset.range (N + 1))
        (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact sq_nonneg _
  calc
    cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => u x i)
        =
      Real.sqrt
        (Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j) ^ 2)) := by
            unfold cubeBesovCircPartialNorm cubeBesovCircPartialSeminorm
            rw [Real.sqrt_eq_rpow]
            norm_num
    _ ≤
        Real.sqrt
          (Finset.sum (Finset.range (N + 1))
            (fun j =>
              (cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2)) := by
                exact Real.sqrt_le_sqrt hsum_le
    _ =
        cubeBesovScaleWeight (-s) Q *
          Real.sqrt
            (Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2)) := by
                exact sqrt_sum_sq_const_mul_eq_componentwise
                  (Finset.range (N + 1))
                  (cubeBesovScaleWeight (-s) Q)
                  (fun j => cubeBesovNegativeVectorDepthSeminorm Q s u j)
                  (cubeBesovScaleWeight_nonneg (-s) Q)
    _ = cubeBesovScaleWeight (-s) Q * cubeBesovNegativeVectorPartialSeminormTwo Q s N u := by
          unfold cubeBesovNegativeVectorPartialSeminormTwo
          rfl

theorem cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ B) :
    cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
      cubeBesovScaleWeight (-s) Q * B := by
  unfold cubeBesovCircNorm
  refine csSup_le ?_ ?_
  · exact cubeBesovCircNormValueSet_nonempty Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)
  · rintro x ⟨N, rfl⟩
    calc
      cubeBesovCircNormEntry Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => u x i)
          = cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) (fun x => u x i) := by
              simp [cubeBesovCircNormEntry]
      _ ≤ cubeBesovScaleWeight (-s) Q *
            cubeBesovNegativeVectorPartialSeminorm Q s (N + 1) u := by
            exact
              cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
                Q s u i (N + 1)
      _ ≤ cubeBesovScaleWeight (-s) Q * B := by
            exact mul_le_mul_of_nonneg_left (hB (N + 1))
              (cubeBesovScaleWeight_nonneg (-s) Q)

theorem norm_cubeAverage_smul_component_le_cutoffDualCoeff_mul_negativeVectorPartialBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (u : Vec d → Vec d) (φ : Vec d → ℝ) (i : Fin d)
    {Bφ B : ℝ}
    (hs : 0 < s)
    (hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (hBφ : 0 ≤ Bφ)
    (hφDual : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ Bφ)
    (hφMem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ)
    (hPartial : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ B) :
    ‖cubeAverage Q (fun x => (φ x • u x) i)‖ ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * Bφ) * B := by
  have hB_nonneg : 0 ≤ B :=
    (cubeBesovNegativeVectorPartialSeminorm_nonneg Q s 0 u).trans (hPartial 0)
  have hpair :
      ‖cubeAverage Q (fun x => (φ x • u x) i)‖ =
        |cubeBesovPairing Q (fun x => u x i) φ| := by
    simp [cubeBesovPairing, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      mul_comm]
  have hdual :=
    abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
      Q s (fun x => u x i) φ hs hui hBφ hφDual hφMem
  have hcirc :
      cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
        cubeBesovScaleWeight (-s) Q * B :=
    cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
      Q s u i hPartial
  have hcoeff_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + s) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  rw [hpair]
  calc
    |cubeBesovPairing Q (fun x => u x i) φ|
        ≤ ((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u x i)) * Bφ := hdual
    _ ≤ ((3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q * B)) * Bφ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcirc hcoeff_nonneg) hBφ
    _ = ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovScaleWeight (-s) Q * Bφ) * B := by ring

theorem sum_abs_apply_le_card_mul_norm {d : ℕ} (v : Vec d) :
    (∑ i : Fin d, |v i|) ≤ (Fintype.card (Fin d) : ℝ) * ‖v‖ := by
  calc
    (∑ i : Fin d, |v i|) ≤ ∑ _i : Fin d, ‖v‖ := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    _ = (Fintype.card (Fin d) : ℝ) * ‖v‖ := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem sum_abs_mul_const_mul_le_card_mul_norm_mul_const_mul_of_nonneg
    {d : ℕ} (v : Vec d) {K W : ℝ}
    (hK : 0 ≤ K) (hW : 0 ≤ W) :
    (∑ i : Fin d, |v i| * (K * W)) ≤
      ((Fintype.card (Fin d) : ℝ) * K) * ‖v‖ * W := by
  have hKW : 0 ≤ K * W := mul_nonneg hK hW
  calc
    (∑ i : Fin d, |v i| * (K * W))
        = ∑ i : Fin d, (K * W) * |v i| := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = (K * W) * ∑ i : Fin d, |v i| := by
          rw [Finset.mul_sum]
    _ ≤ (K * W) * ((Fintype.card (Fin d) : ℝ) * ‖v‖) := by
          exact mul_le_mul_of_nonneg_left (sum_abs_apply_le_card_mul_norm v) hKW
    _ = ((Fintype.card (Fin d) : ℝ) * K) * ‖v‖ * W := by ring

theorem cubeBesovCircNorm_two_two_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBoundTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ B) :
    cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) ≤
      cubeBesovScaleWeight (-s) Q * B := by
  unfold cubeBesovCircNorm
  refine csSup_le ?_ ?_
  · exact cubeBesovCircNormValueSet_nonempty Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i)
  · rintro x ⟨N, rfl⟩
    calc
      cubeBesovCircNormEntry Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => u x i)
          = cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) (fun x => u x i) := by
              simp [cubeBesovCircNormEntry]
      _ ≤ cubeBesovScaleWeight (-s) Q *
            cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u := by
            exact
              cubeBesovCircPartialNorm_two_two_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminormTwo
                Q s u i (N + 1)
      _ ≤ cubeBesovScaleWeight (-s) Q * B := by
            exact mul_le_mul_of_nonneg_left (hB (N + 1))
              (cubeBesovScaleWeight_nonneg (-s) Q)

/-- Componentwise `q = 1` circ control at a larger exponent from the full
vector `q = 2` negative seminorm at a smaller exponent, with the geometric
loss from the exponent gap. -/
theorem cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_gap_geometric_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) {a b : ℝ} (hgap : 0 < a - b)
    (u : Vec d → Vec d) (i : Fin d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q b N u)) :
    cubeBesovCircNorm Q a (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
      cubeBesovScaleWeight (-a) Q *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (a - b)))⁻¹) *
          cubeBesovNegativeVectorSeminormTwo Q b u) := by
  refine
    cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
      Q a u i ?_
  intro N
  have hpartial :
      cubeBesovNegativeVectorPartialSeminorm Q a N u ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (a - b)))⁻¹) *
          cubeBesovNegativeVectorPartialSeminormTwo Q b N u :=
    cubeBesovNegativeVectorPartialSeminorm_le_gap_geometric_mul_partialSeminormTwo
      Q hgap N u
  have hfull :
      cubeBesovNegativeVectorPartialSeminormTwo Q b N u ≤
        cubeBesovNegativeVectorSeminormTwo Q b u := by
    unfold cubeBesovNegativeVectorSeminormTwo
    exact le_csSup hBdd ⟨N, rfl⟩
  exact hpartial.trans
    (mul_le_mul_of_nonneg_left hfull (Real.sqrt_nonneg _))

/-- Componentwise `q = 1` circ control at a larger exponent from a scaled
negative-vector partial bound at a smaller exponent. -/
theorem cubeBesovCircNorm_two_one_component_le_scaleWeight_gap_mul_of_scaled_negativeVectorPartialBound
    {d : ℕ} (Q : TriadicCube d) {r t : ℝ} (ht : t ≤ r)
    (u : Vec d → Vec d) (i : Fin d) {B : ℝ}
    (hB : ∀ N : ℕ,
      cubeBesovScaleWeight (-t) Q * cubeBesovNegativeVectorPartialSeminorm Q t N u ≤ B) :
    cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
      cubeBesovScaleWeight (-(r - t)) Q * B := by
  unfold cubeBesovCircNorm
  refine csSup_le ?_ ?_
  · exact cubeBesovCircNormValueSet_nonempty Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞)
      (fun x => u x i)
  · rintro x ⟨N, rfl⟩
    calc
      cubeBesovCircNormEntry Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => u x i)
          = cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
              (fun x => u x i) := by
              simp [cubeBesovCircNormEntry]
      _ ≤ cubeBesovScaleWeight (-r) Q *
            cubeBesovNegativeVectorPartialSeminorm Q r (N + 1) u := by
            exact
              cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
                Q r u i (N + 1)
      _ ≤ cubeBesovScaleWeight (-(r - t)) Q *
            (cubeBesovScaleWeight (-t) Q *
              cubeBesovNegativeVectorPartialSeminorm Q t (N + 1) u) := by
            exact
              cubeBesovNegativeVectorPartialSeminorm_scale_compare_of_le
                Q (r := r) (t := t) ht (N + 1) u
      _ ≤ cubeBesovScaleWeight (-(r - t)) Q * B := by
            exact mul_le_mul_of_nonneg_left (hB (N + 1))
              (cubeBesovScaleWeight_nonneg (-(r - t)) Q)

theorem cubeLpNorm_two_component_le_cubeLpNorm_two {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → Vec d) (i : Fin d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x i) ≤ cubeLpNorm Q (2 : ℝ≥0∞) u := by
  have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_component_of_memLp u i hu
  have hpoint :
      ∀ᵐ x ∂ normalizedCubeMeasure Q, ‖u x i‖ ≤ (1 : ℝ) * ‖u x‖ := by
    exact Filter.Eventually.of_forall fun x => by
      simpa using (norm_le_pi_norm (u x) i)
  have hle :
      MeasureTheory.eLpNorm (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
        ENNReal.ofReal (1 : ℝ) *
          MeasureTheory.eLpNorm u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul hui.aestronglyMeasurable hpoint (2 : ℝ≥0∞)
  have htop_u :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≠ ∞ := hu.eLpNorm_lt_top.ne
  have htop_ui :
      MeasureTheory.eLpNorm (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≠ ∞ :=
    hui.eLpNorm_lt_top.ne
  have htoReal :
      (MeasureTheory.eLpNorm (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)).toReal ≤
        (MeasureTheory.eLpNorm u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)).toReal := by
    have hle' :
        MeasureTheory.eLpNorm (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
          MeasureTheory.eLpNorm u (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa using hle
    exact ENNReal.toReal_mono htop_u hle'
  simpa [cubeLpNorm] using htoReal

theorem cubeBesovOscillation_two_component_le_cubeLpNorm_fluctuationVec {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (i : Fin d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x i) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u) := by
  have hfluct : MeasureTheory.MemLp (cubeFluctuationVec Q u)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q u hu
  simpa [cubeBesovOscillation, cubeFluctuation_component_eq_cubeFluctuationVec_component Q u i] using
    cubeLpNorm_two_component_le_cubeLpNorm_two Q (cubeFluctuationVec Q u) i hfluct

theorem cubeBesovDepthAverage_two_component_le_positiveVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (i : Fin d) (j : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j ≤
      cubeBesovPositiveVectorDepthAverage Q u j := by
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R hR
  have huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
  have hlocal :
      cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u x i) ≤
        cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u) :=
    cubeBesovOscillation_two_component_le_cubeLpNorm_fluctuationVec R u i huR
  have hsq :
      (cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u x i)) ^ (2 : ℕ) ≤
        (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u)) ^ (2 : ℕ) := by
    have hleft_nonneg : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) (fun x => u x i) :=
      cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) (fun x => u x i)
    have hright_nonneg : 0 ≤ cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u) :=
      cubeLpNorm_nonneg R (2 : ℝ≥0∞) (cubeFluctuationVec R u)
    nlinarith
  simpa [cubeBesovDepthAverage, cubeBesovPositiveVectorDepthAverage, Real.rpow_natCast]
    using hsq

theorem cubeBesovDepthWeight_eq_scaleWeight_mul_rpow {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovDepthWeight Q s j =
      cubeBesovScaleWeight s Q * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
  have hQ_nonneg : 0 ≤ cubeScaleFactor Q := cubeVolume_nonneg Q |> fun _ => by
    simpa [cubeScaleFactor] using
      (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
  calc
    cubeBesovDepthWeight Q s j
        = (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s) := by
            rfl
    _ = (cubeScaleFactor Q) ^ (-s) / ((3 : ℝ) ^ j) ^ (-s) := by
          exact Real.div_rpow hQ_nonneg (by positivity) (-s)
    _ = (cubeScaleFactor Q ^ s)⁻¹ / (((3 : ℝ) ^ j) ^ s)⁻¹ := by
          rw [Real.rpow_neg hQ_nonneg, Real.rpow_neg (show 0 ≤ ((3 : ℝ) ^ j) by positivity)]
    _ = (cubeScaleFactor Q ^ s)⁻¹ * ((3 : ℝ) ^ j) ^ s := by
          rw [div_eq_mul_inv, inv_inv]
    _ = (cubeScaleFactor Q) ^ (-s) * ((3 : ℝ) ^ j) ^ s := by
          rw [← Real.rpow_neg hQ_nonneg]
    _ = (cubeScaleFactor Q) ^ (-s) * Real.rpow (3 : ℝ) ((j : ℝ) * s) := by
          congr 1
          symm
          simpa [mul_comm] using Real.rpow_natCast_mul (by positivity : 0 ≤ (3 : ℝ)) j s
    _ = (cubeScaleFactor Q) ^ (-s) * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
          congr 1
          rw [mul_comm]
    _ = cubeBesovScaleWeight s Q * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
          simp [cubeBesovScaleWeight]

theorem cubeBesovDepthSeminorm_two_component_le_scaleWeight_mul_positiveVectorDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (j : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j ≤
      cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s u j := by
  have havg :
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j ≤
        cubeBesovPositiveVectorDepthAverage Q u j :=
    cubeBesovDepthAverage_two_component_le_positiveVectorDepthAverage Q u i j hu
  have hsqrt :
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j) ≤
        Real.sqrt (cubeBesovPositiveVectorDepthAverage Q u j) := by
    exact Real.sqrt_le_sqrt havg
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j :=
    cubeBesovDepthWeight_nonneg Q s j
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j
        = cubeBesovDepthWeight Q s j *
            Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) (fun x => u x i) j) := by
              simp [cubeBesovDepthSeminorm, Real.sqrt_eq_rpow]
    _ ≤ cubeBesovDepthWeight Q s j *
          Real.sqrt (cubeBesovPositiveVectorDepthAverage Q u j) := by
            exact mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ = cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s u j := by
          rw [cubeBesovDepthWeight_eq_scaleWeight_mul_rpow]
          simp [cubeBesovPositiveVectorDepthSeminorm, mul_assoc]

theorem cubeBesovPartialSeminorm_two_component_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => u x i) ≤
      cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  have hsum_le :
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j) ^ 2)
        ≤
      Finset.sum (Finset.range (N + 1))
          (fun j =>
            (cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hdepth :=
      cubeBesovDepthSeminorm_two_component_le_scaleWeight_mul_positiveVectorDepthSeminorm
        Q s u i j hu
    have hleft_nonneg :
        0 ≤ cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j :=
      cubeBesovDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) (fun x => u x i) j
    have hright_nonneg :
        0 ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s u j := by
      exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q)
        (cubeBesovPositiveVectorDepthSeminorm_nonneg Q s u j)
    nlinarith
  have hsum_nonneg :
      0 ≤ Finset.sum (Finset.range (N + 1))
        (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact sq_nonneg _
  calc
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => u x i)
        =
      Real.sqrt
        (Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j) ^ 2)) := by
            unfold cubeBesovPartialSeminorm
            rw [Real.sqrt_eq_rpow]
            norm_num
    _ ≤
        Real.sqrt
          (Finset.sum (Finset.range (N + 1))
            (fun j =>
              (cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2)) := by
                exact Real.sqrt_le_sqrt hsum_le
    _ =
        cubeBesovScaleWeight s Q *
          Real.sqrt
            (Finset.sum (Finset.range (N + 1))
              (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2)) := by
                exact sqrt_sum_sq_const_mul_eq_componentwise
                  (Finset.range (N + 1))
                  (cubeBesovScaleWeight s Q)
                  (fun j => cubeBesovPositiveVectorDepthSeminorm Q s u j)
                  (cubeBesovScaleWeight_nonneg s Q)
    _ = cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
          unfold cubeBesovPositiveVectorPartialSeminormTwo
          rfl

theorem cubeBesovPartialSeminormTop_two_component_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N (fun x => u x i) ≤
      cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  classical
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le
    (s := Finset.range (N + 1))
    (H := ⟨0, by simp⟩)
    (f := fun j : ℕ => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j) ?_
  intro j hj
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => u x i) j
        ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s u j := by
            exact cubeBesovDepthSeminorm_two_component_le_scaleWeight_mul_positiveVectorDepthSeminorm
              Q s u i j hu
    _ ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
          exact mul_le_mul_of_nonneg_left
            (cubeBesovPositiveVectorDepthSeminorm_le_partialSeminormTwo Q s u N j hj)
            (cubeBesovScaleWeight_nonneg s Q)

theorem cubeBesovDualLocalMemLpGlobal_component_of_memLp {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (i : Fin d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => u x i) := by
  have hpConj :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  intro j R hR
  have huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
  have hfluctR : MeasureTheory.MemLp (cubeFluctuationVec R u)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_cubeFluctuationVec R u huR
  simpa [hpConj, cubeFluctuation_component_eq_cubeFluctuationVec_component R u i] using!
    (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hfluctR

/-- A scalar `L²` function is locally admissible as a `p = 2` Besov dual test
at every descendant scale. -/
theorem cubeBesovDualLocalMemLpGlobal_of_memLp_two {d : ℕ}
    (Q : TriadicCube d) (g : Vec d → ℝ)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g := by
  have hpConj :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  intro j R hR
  have hgR : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp_generic (E := ℝ) hR hg
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage R g)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    MeasureTheory.memLp_const (cubeAverage R g)
  simpa [hpConj, cubeFluctuation] using! hgR.sub hconst

theorem cubeBesovDualTestNorm_two_one_component_cubeFluctuationVec_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q u x i) ≤
      cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  have hconj :
      cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have havg :
      cubeAverage Q (fun x => cubeFluctuationVec Q u x i) = 0 := by
    simpa [cubeFluctuation_component_eq_cubeFluctuationVec_component Q u i] using
      cubeAverage_cubeFluctuation Q (fun x => u x i)
  have hmem :
      ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro j hj R hR
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
  have hpartial_eq :
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (cubeFluctuationVec Q u) =
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
    simpa [cubeFluctuationVec] using!
      cubeBesovPositiveVectorPartialSeminormTwo_sub_const Q s N u (cubeAverageVec Q u)
        (fun j hj R hR => hmem j hj R hR)
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
    N (fun x => cubeFluctuationVec Q u x i) hconj]
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    Q s (cubeBesovConjExponent (2 : ℝ≥0∞)) N (fun x => cubeFluctuationVec Q u x i) havg]
  calc
    cubeBesovPartialSeminormTop Q s (cubeBesovConjExponent (2 : ℝ≥0∞)) N
        (fun x => cubeFluctuationVec Q u x i)
        ≤ cubeBesovScaleWeight s Q *
            cubeBesovPositiveVectorPartialSeminormTwo Q s N (cubeFluctuationVec Q u) := by
            simpa [hpConj] using
              cubeBesovPartialSeminormTop_two_component_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
                Q s (cubeFluctuationVec Q u) i N (memLp_cubeFluctuationVec Q u hu)
    _ = cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
          rw [hpartial_eq]

theorem cubeBesovDualTestNorm_two_two_component_cubeFluctuationVec_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (i : Fin d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q u x i) ≤
      cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hq : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  have havg :
      cubeAverage Q (fun x => cubeFluctuationVec Q u x i) = 0 := by
    simpa [cubeFluctuation_component_eq_cubeFluctuationVec_component Q u i] using
      cubeAverage_cubeFluctuation Q (fun x => u x i)
  have hmem :
      ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro j hj R hR
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
  have hpartial_eq :
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (cubeFluctuationVec Q u) =
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
    simpa [cubeFluctuationVec] using!
      cubeBesovPositiveVectorPartialSeminormTwo_sub_const Q s N u (cubeAverageVec Q u)
        (fun j hj R hR => hmem j hj R hR)
  rw [cubeBesovDualTestNorm_eq_cubeBesovDualTestSeminorm_of_cubeAverage_eq_zero
    Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => cubeFluctuationVec Q u x i) havg]
  rw [cubeBesovDualTestSeminorm_of_conjExponent_ne_top Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
    (fun x => cubeFluctuationVec Q u x i) hq]
  calc
    cubeBesovPartialSeminorm Q s (cubeBesovConjExponent (2 : ℝ≥0∞))
        (cubeBesovConjExponent (2 : ℝ≥0∞)) N (fun x => cubeFluctuationVec Q u x i)
        ≤ cubeBesovScaleWeight s Q *
            cubeBesovPositiveVectorPartialSeminormTwo Q s N (cubeFluctuationVec Q u) := by
            simpa [hpConj] using
              cubeBesovPartialSeminorm_two_component_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
                Q s (cubeFluctuationVec Q u) i N (memLp_cubeFluctuationVec Q u hu)
    _ = cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
          rw [hpartial_eq]

theorem abs_cubeAverage_vecDot_fluctuationVec_le_sum_note_terms_of_partialBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hBscale_nonneg : 0 ≤ cubeBesovScaleWeight s Q * Bg :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBg
  have hu_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp u i hu
  have hgFluct :
      MeasureTheory.MemLp (cubeFluctuationVec Q g) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q g hg
  have hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i) ≤
            cubeBesovScaleWeight s Q * Bg := by
    intro i N
    calc
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i)
          ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
              exact
                cubeBesovDualTestNorm_two_one_component_cubeFluctuationVec_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
                  Q s g i N hg
      _ ≤ cubeBesovScaleWeight s Q * Bg := by
            exact mul_le_mul_of_nonneg_left (hpos N) (cubeBesovScaleWeight_nonneg s Q)
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => cubeFluctuationVec Q g x i) := by
    intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q (cubeFluctuationVec Q g) i hgFluct
  calc
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))|
        ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
            exact
              abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_one_of_nonneg
                Q s u (cubeFluctuationVec Q g) (fun _ => cubeBesovScaleWeight s Q * Bg)
                hs hu_comp (fun _ => hBscale_nonneg) hnorm hmem
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcomponent :
              cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
                cubeBesovScaleWeight (-s) Q * Bu := by
            exact
              cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
                Q s u i hneg
          exact mul_le_mul_of_nonneg_right
            (add_le_add
              (mul_le_mul_of_nonneg_left hcomponent
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
              le_rfl)
            hBscale_nonneg

/-- Sharp fluctuation estimate without the redundant average tail on the
negative Besov side.  This is the bridge form of the sharp vectorized duality
bound used in the note-facing Caccioppoli proof. -/
theorem abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| ≤
      (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hBscale_nonneg : 0 ≤ cubeBesovScaleWeight s Q * Bg :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBg
  have hu_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp u i hu
  have hgFluct :
      MeasureTheory.MemLp (cubeFluctuationVec Q g) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q g hg
  have hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i) ≤
            cubeBesovScaleWeight s Q * Bg := by
    intro i N
    calc
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i)
          ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
              exact
                cubeBesovDualTestNorm_two_one_component_cubeFluctuationVec_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
                  Q s g i N hg
      _ ≤ cubeBesovScaleWeight s Q * Bg := by
            exact mul_le_mul_of_nonneg_left (hpos N) (cubeBesovScaleWeight_nonneg s Q)
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => cubeFluctuationVec Q g x i) := by
    intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q (cubeFluctuationVec Q g) i hgFluct
  calc
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))|
        ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
            exact
              abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_one_of_nonneg
                Q s u (cubeFluctuationVec Q g) (fun _ => cubeBesovScaleWeight s Q * Bg)
                hs hu_comp (fun _ => hBscale_nonneg) hnorm hmem
    _ ≤ ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcomponent :
              cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
                cubeBesovScaleWeight (-s) Q * Bu := by
            exact
              cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
                Q s u i hneg
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcomponent
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
            hBscale_nonneg
    _ = (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          simp

/-- Sharp fluctuation estimate with the positive-side input stated directly as
componentwise dual-test bounds. This avoids forcing callers through the finite
`q = 2` positive Besov package when they already have an infinite-depth
`q = ∞` cutoff-product estimate. -/
theorem abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_dualTestBounds
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm Q s N u ≤ Bu)
    (hdual : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuationVec Q g x i) ≤ cubeBesovScaleWeight s Q * Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| ≤
      (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hBscale_nonneg : 0 ≤ cubeBesovScaleWeight s Q * Bg :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBg
  have hu_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp u i hu
  have hgFluct :
      MeasureTheory.MemLp (cubeFluctuationVec Q g) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q g hg
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
          (fun x => cubeFluctuationVec Q g x i) := by
    intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp
      Q (cubeFluctuationVec Q g) i hgFluct
  calc
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))|
        ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
            exact
              abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_one_of_nonneg
                Q s u (cubeFluctuationVec Q g)
                (fun _ => cubeBesovScaleWeight s Q * Bg)
                hs hu_comp (fun _ => hBscale_nonneg) hdual hmem
    _ ≤ ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcomponent :
              cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) ≤
                cubeBesovScaleWeight (-s) Q * Bu := by
            exact
              cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBound
                Q s u i hneg
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcomponent
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
            hBscale_nonneg
    _ = (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          simp

theorem abs_cubeAverage_vecDot_fluctuationVec_le_sum_note_terms_of_partialBounds_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hBscale_nonneg : 0 ≤ cubeBesovScaleWeight s Q * Bg :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBg
  have hu_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp u i hu
  have hgFluct :
      MeasureTheory.MemLp (cubeFluctuationVec Q g) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q g hg
  have hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i) ≤
            cubeBesovScaleWeight s Q * Bg := by
    intro i N
    calc
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i)
          ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
              exact
                cubeBesovDualTestNorm_two_two_component_cubeFluctuationVec_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
                  Q s g i N hg
      _ ≤ cubeBesovScaleWeight s Q * Bg := by
            exact mul_le_mul_of_nonneg_left (hpos N) (cubeBesovScaleWeight_nonneg s Q)
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => cubeFluctuationVec Q g x i) := by
    intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q (cubeFluctuationVec Q g) i hgFluct
  calc
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))|
        ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
          cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
          (cubeBesovScaleWeight s Q * Bg)) := by
            exact
              abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_two_of_nonneg
                Q s u (cubeFluctuationVec Q g) (fun _ => cubeBesovScaleWeight s Q * Bg)
                hs hu_comp (fun _ => hBscale_nonneg) hnorm hmem
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcomponent :
              cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) ≤
                cubeBesovScaleWeight (-s) Q * Bu := by
            exact
              cubeBesovCircNorm_two_two_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBoundTwo
                Q s u i hneg
          exact mul_le_mul_of_nonneg_right
            (add_le_add
              (mul_le_mul_of_nonneg_left hcomponent
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
              le_rfl)
            hBscale_nonneg

/-- Sharp `q = 2` fluctuation estimate without the redundant average tail on
the negative Besov side. -/
theorem abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) {Bu Bg : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu)
    (hpos : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N g ≤ Bg) :
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))| ≤
      (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
  have hBscale_nonneg : 0 ≤ cubeBesovScaleWeight s Q * Bg :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBg
  have hu_comp :
      ∀ i : Fin d, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_component_of_memLp u i hu
  have hgFluct :
      MeasureTheory.MemLp (cubeFluctuationVec Q g) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q g hg
  have hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i) ≤
            cubeBesovScaleWeight s Q * Bg := by
    intro i N
    calc
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => cubeFluctuationVec Q g x i)
          ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
              exact
                cubeBesovDualTestNorm_two_two_component_cubeFluctuationVec_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
                  Q s g i N hg
      _ ≤ cubeBesovScaleWeight s Q * Bg := by
            exact mul_le_mul_of_nonneg_left (hpos N) (cubeBesovScaleWeight_nonneg s Q)
  have hmem :
      ∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => cubeFluctuationVec Q g x i) := by
    intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q (cubeFluctuationVec Q g) i hgFluct
  calc
    |cubeAverage Q (fun x => vecDot (u x) (cubeFluctuationVec Q g x))|
        ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i)) *
          (cubeBesovScaleWeight s Q * Bg)) := by
            exact
              abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_two_of_nonneg
                Q s u (cubeFluctuationVec Q g) (fun _ => cubeBesovScaleWeight s Q * Bg)
                hs hu_comp (fun _ => hBscale_nonneg) hnorm hmem
    _ ≤ ∑ i : Fin d, (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcomponent :
              cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) ≤
                cubeBesovScaleWeight (-s) Q * Bu := by
            exact
              cubeBesovCircNorm_two_two_component_le_scaleWeight_neg_mul_of_negativeVectorPartialBoundTwo
                Q s u i hneg
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcomponent
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
            hBscale_nonneg
    _ = (d : ℝ) * (((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bu)) *
        (cubeBesovScaleWeight s Q * Bg)) := by
          simp

end

end Homogenization
