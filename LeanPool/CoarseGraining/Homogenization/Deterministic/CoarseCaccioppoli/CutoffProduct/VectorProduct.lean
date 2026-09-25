/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms

/-! # Vector Product -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeL2Scalar_scale_depth_term_eq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      (descendantsAverage Q j
        (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)) ^ (1 / 2 : ℝ) =
      cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by
  have hfactor :
      descendantsAverage Q j
        (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2) =
          (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2 * cubeL2ScalarDepthAverage Q v j := by
    calc
      descendantsAverage Q j
          (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)
          =
            descendantsAverage Q j
              (fun R => ((cubeScaleFactor Q / (3 : ℝ) ^ j) *
                cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2) := by
                  unfold descendantsAverage
                  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro R hR
                  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
      _ =
          descendantsAverage Q j
            (fun R => (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2 *
              (cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2) := by
                refine congrArg (descendantsAverage Q j) ?_
                funext R
                ring
      _ = (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2 * cubeL2ScalarDepthAverage Q v j := by
            rw [descendantsAverage_mul_left Q j
              ((cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2)
              (fun R => (cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)]
            rfl
  have havg_nonneg : 0 ≤ cubeL2ScalarDepthAverage Q v j := cubeL2ScalarDepthAverage_nonneg Q v j
  have hscale_nonneg : 0 ≤ cubeScaleFactor Q / (3 : ℝ) ^ j := by
    exact div_nonneg (cubeScaleFactor_nonneg Q) (by positivity)
  have hmain :
      (descendantsAverage Q j
        (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)) ^ (1 / 2 : ℝ) =
        (cubeScaleFactor Q / (3 : ℝ) ^ j) * Real.sqrt (cubeL2ScalarDepthAverage Q v j) := by
    rw [hfactor, Real.mul_rpow (sq_nonneg _) havg_nonneg]
    rw [sq_rpow_half_eq_of_nonneg hscale_nonneg]
    rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        (descendantsAverage Q j
          (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)) ^ (1 / 2 : ℝ)
        =
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            ((cubeScaleFactor Q / (3 : ℝ) ^ j) * Real.sqrt (cubeL2ScalarDepthAverage Q v j)) := by
              rw [hmain]
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) * (cubeScaleFactor Q / (3 : ℝ) ^ j)) *
          Real.sqrt (cubeL2ScalarDepthAverage Q v j) := by
            ring
    _ =
        (cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ))) *
          Real.sqrt (cubeL2ScalarDepthAverage Q v j) := by
            congr 1
            have hpow :
                Real.rpow (3 : ℝ) (s * (j : ℝ)) * (cubeScaleFactor Q / (3 : ℝ) ^ j) =
                  cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) := by
              have hnat : (3 : ℝ) ^ j = Real.rpow (3 : ℝ) (j : ℝ) := by
                symm
                exact Real.rpow_natCast (3 : ℝ) j
              calc
                Real.rpow (3 : ℝ) (s * (j : ℝ)) * (cubeScaleFactor Q / (3 : ℝ) ^ j)
                    =
                      cubeScaleFactor Q *
                        (Real.rpow (3 : ℝ) (s * (j : ℝ)) * ((3 : ℝ) ^ j)⁻¹) := by
                            ring
                _ =
                    cubeScaleFactor Q *
                      (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                        (Real.rpow (3 : ℝ) (j : ℝ))⁻¹) := by
                          rw [hnat]
                _ =
                    cubeScaleFactor Q *
                      (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                        Real.rpow (3 : ℝ) (-(j : ℝ))) := by
                          congr 1
                          rw [show (Real.rpow (3 : ℝ) (j : ℝ))⁻¹ =
                              Real.rpow (3 : ℝ) (-(j : ℝ)) by
                            symm
                            exact Real.rpow_neg (by positivity : 0 ≤ (3 : ℝ)) (j : ℝ)]
                _ =
                    cubeScaleFactor Q *
                      Real.rpow (3 : ℝ) (s * (j : ℝ) + -(j : ℝ)) := by
                          congr 1
                          exact
                            (Real.rpow_add (by positivity : 0 < (3 : ℝ))
                              (s * (j : ℝ)) (-(j : ℝ))).symm
                _ = cubeScaleFactor Q * Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) := by
                      congr 1
                      ring_nf
            rw [hpow]
    _ = cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by
          simp [cubeL2ScalarDepthSeminorm, mul_assoc]

theorem cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (j : ℕ) (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j ≤
      2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
        cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
  let A : TriadicCube d → ℝ :=
    fun R => (cubeScaleFactor R * B) * cubeLpNorm R (2 : ℝ≥0∞) v
  let C : TriadicCube d → ℝ :=
    fun R => cubeLpNorm Q ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v
  have hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x)) ≤
          2 * (A R + C R) := by
    intro R hR
    have hvR : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := ℝ) hR hv
    have hξR : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hξLp
    have hcutoffR :
        cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x)) ≤
          2 * ((cubeScaleFactor R * B) * cubeLpNorm R (2 : ℝ≥0∞) v +
            cubeLpNorm R ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v) := by
      exact
        cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
          R v ξ hB hvR hξR hξ
            (fun i z hz => hderiv i z (cubeSet_subset_of_mem_descendantsAtDepth hR hz))
    have hosc_nonneg : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) v :=
      cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) v
    have hlinfty :
        cubeLpNorm R ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v ≤
          cubeLpNorm Q ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v := by
      exact mul_le_mul_of_nonneg_right
        (cubeLpNorm_infty_descendant_le hR ξ hξLp) hosc_nonneg
    calc
      cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x))
          ≤ 2 * ((cubeScaleFactor R * B) * cubeLpNorm R (2 : ℝ≥0∞) v +
              cubeLpNorm R ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v) := hcutoffR
      _ ≤ 2 * ((cubeScaleFactor R * B) * cubeLpNorm R (2 : ℝ≥0∞) v +
            cubeLpNorm Q ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v) := by
            exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hlinfty) (by norm_num)
      _ = 2 * (A R + C R) := by
            simp [A, C]
  have hA_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (cubeScaleFactor_nonneg R) hB)
      (cubeLpNorm_nonneg R (2 : ℝ≥0∞) v)
  have hC_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ C R := by
    intro R hR
    exact mul_nonneg
      (cubeLpNorm_nonneg Q ∞ ξ)
      (cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) v)
  have hsq_bound :
      descendantsAverage Q j
        (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2) ≤
        descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hleft_nonneg :
        0 ≤ cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuationVec R (fun x => v x • ξ x)) :=
      cubeLpNorm_nonneg R (2 : ℝ≥0∞) (cubeFluctuationVec R (fun x => v x • ξ x))
    have hright_nonneg : 0 ≤ 2 * (A R + C R) := by
      exact mul_nonneg (by norm_num) (add_nonneg (hA_nonneg R hR) (hC_nonneg R hR))
    nlinarith [hlocal R hR, hleft_nonneg, hright_nonneg]
  have hleft_nonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hroot_bound :
      Real.sqrt (descendantsAverage Q j
        (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2)) ≤
        Real.sqrt (descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2)) := by
    exact Real.sqrt_le_sqrt hsq_bound
  have hconst :
      Real.sqrt (descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2)) =
        2 * Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2)) := by
    rw [descendantsAverage_sqrt_const_mul_eq Q j 2 (fun R => A R + C R) (by norm_num)]
  have hsplit :
      Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2)) ≤
        Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) +
          Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)) :=
    descendantsAverage_sqrt_add_le Q j A C hA_nonneg hC_nonneg
  have hAterm :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) =
          cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by
    have hArew :
        descendantsAverage Q j (fun R => (A R) ^ 2) =
          descendantsAverage Q j
            (fun R => (B * (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v)) ^ 2) := by
      refine congrArg (descendantsAverage Q j) ?_
      funext R
      simp [A]
      ring
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2))
          =
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j
                (fun R => (B * (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v)) ^ 2)) := by
                  rw [hArew]
      _ =
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (B *
              Real.sqrt (descendantsAverage Q j
                (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2))) := by
                  rw [descendantsAverage_sqrt_const_mul_eq Q j B
                    (fun R => cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) hB]
      _ = B *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j
              (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2))) := by
                ring
      _ = B * (cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j) := by
            rw [show Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                Real.sqrt (descendantsAverage Q j
                  (fun R => (cubeScaleFactor R * cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)) =
                  cubeScaleFactor Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j by
              simpa [Real.sqrt_eq_rpow] using cubeL2Scalar_scale_depth_term_eq Q s v j]
      _ = cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j := by
            ring
  have hCterm :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)) =
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j := by
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2))
          =
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt (descendantsAverage Q j
                (fun R => (cubeLpNorm Q ∞ ξ * cubeBesovOscillation R (2 : ℝ≥0∞) v) ^ 2)) := by
                  simp [C]
      _ =
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (cubeLpNorm Q ∞ ξ *
              Real.sqrt (descendantsAverage Q j
                (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) v) ^ 2))) := by
                  rw [descendantsAverage_sqrt_const_mul_eq Q j (cubeLpNorm Q ∞ ξ)
                    (fun R => cubeBesovOscillation R (2 : ℝ≥0∞) v)
                    (cubeLpNorm_nonneg Q ∞ ξ)]
      _ = cubeLpNorm Q ∞ ξ *
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j
              (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) v) ^ 2))) := by
                ring
      _ = cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j := by
            rfl
  calc
    cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j
        =
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j
              (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
                (cubeFluctuationVec R (fun x => v x • ξ x))) ^ 2)) := by
              simp [cubeBesovPositiveVectorDepthSeminorm, cubeBesovPositiveVectorDepthAverage]
    _ ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (2 * (A R + C R)) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hroot_bound (Real.rpow_nonneg (by positivity) _)
    _ = Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (2 * Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2))) := by
            rw [hconst]
    _ = 2 * (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2))) := by
            ring
    _ ≤ 2 * (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) +
              Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)))) := by
            have hinner :
                Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                    Real.sqrt (descendantsAverage Q j (fun R => (A R + C R) ^ 2))
                  ≤
                Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                    (Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) +
                      Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2))) := by
              exact mul_le_mul_of_nonneg_left hsplit
                (Real.rpow_nonneg (by positivity : 0 ≤ (3 : ℝ)) _)
            exact mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = 2 * ((Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2))) +
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (descendantsAverage Q j (fun R => (C R) ^ 2)))) := by
            ring
    _ = 2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
            rw [hAterm, hCterm]

theorem cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => v x • ξ x) ≤
      2 * (cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v +
        cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
  let A : ℕ → ℝ := fun j => cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j
  let C : ℕ → ℝ := fun j => cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j
  have hA_nonneg : ∀ j ∈ Finset.range (N + 1), 0 ≤ A j := by
    intro j hj
    exact mul_nonneg
      (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
      (cubeL2ScalarDepthSeminorm_nonneg Q (s - 1) v j)
  have hC_nonneg : ∀ j ∈ Finset.range (N + 1), 0 ≤ C j := by
    intro j hj
    exact mul_nonneg
      (cubeLpNorm_nonneg Q ∞ ξ)
      (cubeBesovPositiveScalarDepthSeminorm_nonneg Q s v j)
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j ≤
          2 * (A j + C j) := by
    intro j hj
    simpa [A, C] using
      cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
        Q s j v ξ hB hv hξLp hξ hderiv
  have hsq_bound :
      ∑ j ∈ Finset.range (N + 1),
        (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j) ^ 2
        ≤
      ∑ j ∈ Finset.range (N + 1), (2 * (A j + C j)) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hleft_nonneg : 0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j :=
      cubeBesovPositiveVectorDepthSeminorm_nonneg Q s (fun x => v x • ξ x) j
    have hright_nonneg : 0 ≤ 2 * (A j + C j) := by
      exact mul_nonneg (by norm_num) (add_nonneg (hA_nonneg j hj) (hC_nonneg j hj))
    nlinarith [hdepth j hj, hleft_nonneg, hright_nonneg]
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.range (N + 1),
        (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j) ^ 2 := by
    exact Finset.sum_nonneg fun j hj => sq_nonneg _
  have hroot_bound :
      Real.sqrt (∑ j ∈ Finset.range (N + 1),
        (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j) ^ 2) ≤
      Real.sqrt (∑ j ∈ Finset.range (N + 1), (2 * (A j + C j)) ^ 2) := by
    exact Real.sqrt_le_sqrt hsq_bound
  have hsplit :
      Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j + C j) ^ 2) ≤
        Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j) ^ 2) +
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (C j) ^ 2) :=
    sqrt_sum_sq_add_le_sqrt (Finset.range (N + 1)) A C hA_nonneg hC_nonneg
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => v x • ξ x)
        = Real.sqrt (∑ j ∈ Finset.range (N + 1),
            (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => v x • ξ x) j) ^ 2) := by
              rfl
    _ ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1), (2 * (A j + C j)) ^ 2) := hroot_bound
    _ = 2 * Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j + C j) ^ 2) := by
          rw [sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) 2 (fun j => A j + C j) (by norm_num)]
    _ ≤ 2 * (Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j) ^ 2) +
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (C j) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hsplit ?_
            norm_num
    _ = 2 * (cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v) := by
          rw [show Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j) ^ 2) =
              cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N v by
                unfold A cubeL2ScalarPartialSeminormTwo
                exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1))
                  (cubeScaleFactor Q * B) (fun j => cubeL2ScalarDepthSeminorm Q (s - 1) v j)
                  (mul_nonneg (cubeScaleFactor_nonneg Q) hB)]
          rw [show Real.sqrt (∑ j ∈ Finset.range (N + 1), (C j) ^ 2) =
              cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N v by
                unfold C cubeBesovPositiveScalarPartialSeminormTwo
                exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1))
                  (cubeLpNorm Q ∞ ξ) (fun j => cubeBesovPositiveScalarDepthSeminorm Q s v j)
                  (cubeLpNorm_nonneg Q ∞ ξ)]

theorem cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (u x - cubeAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (fun x => u x - cubeAverage Q u) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (fun x => u x - cubeAverage Q u)) := by
  have hu_centered :
      MeasureTheory.MemLp (fun x => u x - cubeAverage Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  simpa using
    cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
      Q s N (fun x => u x - cubeAverage Q u) ξ hB hu_centered hξLp hξ hderiv

theorem cubeLpNorm_two_le_cubeBesovPartialNormTop_zero {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) v ≤ cubeBesovPartialNormTop Q 0 (2 : ℝ≥0∞) 0 v := by
  have hv_fluct :
      MeasureTheory.MemLp (cubeFluctuation Q v) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hv.sub (MeasureTheory.memLp_const (cubeAverage Q v))
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage Q v)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (cubeAverage Q v)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) v
        = cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => cubeFluctuation Q v x + (fun _ : Vec d => cubeAverage Q v) x) := by
              congr 1
              funext x
              simp [cubeFluctuation]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v) +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => cubeAverage Q v) := by
            exact cubeLpNorm_add_le Q (2 : ℝ≥0∞)
              (cubeFluctuation Q v) (fun _ : Vec d => cubeAverage Q v)
              hv_fluct hconst (by norm_num)
    _ = cubeBesovOscillation Q (2 : ℝ≥0∞) v + ‖cubeAverage Q v‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞)) (c := cubeAverage Q v) (by norm_num)]
          simp [cubeBesovOscillation]
    _ = cubeBesovPartialNormTop Q 0 (2 : ℝ≥0∞) 0 v := by
          have hosc_nonneg : 0 ≤ cubeBesovOscillation Q (2 : ℝ≥0∞) v :=
            cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) v
          have hsq :
              (cubeBesovOscillation Q (2 : ℝ≥0∞) v ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) =
                cubeBesovOscillation Q (2 : ℝ≥0∞) v := by
            simpa using sq_rpow_half_eq_of_nonneg hosc_nonneg
          simp [cubeBesovPartialNormTop, cubeBesovPartialSeminormTop, cubeBesovDepthSeminorm,
            cubeBesovDepthAverage_depth_zero, cubeBesovDepthWeight_depth_zero, cubeBesovScaleWeight]
          simpa using hsq.symm

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.restrict_to_descendant
    {d : ℕ} {Q R : TriadicCube d} {C : ℝ} {u g : Vec d → ℝ} {M j : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hR : R ∈ descendantsAtDepth Q j) (hj : j ≤ M) :
    CubeDescendantProjectedDualMeanZeroPoincareEstimate R C u g (M - j) := by
  intro n hn S hS
  have hn_le : n ≤ M - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hjn_le : j + n ≤ M := by
    simpa [Nat.add_sub_of_le hj] using Nat.add_le_add_left hn_le j
  have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
  have hmem : j + n ∈ Finset.range (M + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjn_le)
  have hbase := hproj (j + n) hmem S hSQ
  have hsub : M - (j + n) = (M - j) - n := by
    omega
  simpa [hsub] using hbase

theorem cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ) (j : ℕ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeL2ScalarDepthAverage Q v j = (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 := by
  have hnorm_int :
      MeasureTheory.IntegrableOn (fun x => ‖v x‖ ^ (2 : ℝ))
        (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hv.integrable_norm_rpow (by norm_num) (by norm_num))
  calc
    cubeL2ScalarDepthAverage Q v j
        = descendantsAverage Q j (fun R => cubeAverage R (fun x => ‖v x‖ ^ (2 : ℝ))) := by
            unfold cubeL2ScalarDepthAverage descendantsAverage
            refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            simpa using
              (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := R) (p := (2 : ℝ≥0∞))
                (f := v) (by norm_num) (by norm_num)
                (memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hv))
    _ = cubeAverage Q (fun x => ‖v x‖ ^ (2 : ℝ)) := by
          rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
            (Q := Q) (j := j) (f := fun x => ‖v x‖ ^ (2 : ℝ)) hnorm_int]
    _ = (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 := by
          simpa using
            (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := Q) (p := (2 : ℝ≥0∞))
              (f := v) (by norm_num) (by norm_num) hv).symm

theorem cubeL2ScalarDepthSeminorm_eq_rpow_mul_cubeLpNorm_two {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeL2ScalarDepthSeminorm Q s v j =
      Real.rpow (3 : ℝ) (s * (j : ℝ)) * cubeLpNorm Q (2 : ℝ≥0∞) v := by
  rw [cubeL2ScalarDepthSeminorm, cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q v j hv]
  rw [Real.sqrt_sq_eq_abs]
  simp [abs_of_nonneg (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v)]

theorem cubeBesovPartialNormTop_zero_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (v : Vec d → ℝ) :
    cubeBesovPartialNormTop Q s p 0 v ≤ cubeBesovPartialNormTop Q s p N v := by
  unfold cubeBesovPartialNormTop cubeBesovPartialSeminormTop
  refine add_le_add ?_ le_rfl
  simpa using
    (Finset.le_sup' (s := Finset.range (N + 1))
      (f := fun j => cubeBesovDepthSeminorm Q s p v j) (by simp : 0 ∈ Finset.range (N + 1)))

theorem rpow_three_weight_sq_eq_geometric_ratio_pow (s : ℝ) (j : ℕ) :
    (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 = (Real.rpow (3 : ℝ) (2 * s)) ^ j := by
  calc
    (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2
        = Real.rpow (Real.rpow (3 : ℝ) (s * (j : ℝ))) (2 : ℝ) := by
            symm
            exact Real.rpow_natCast _ 2
    _ = Real.rpow (3 : ℝ) ((s * (j : ℝ)) * 2) := by
          simpa using
            (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (s * (j : ℝ)) (2 : ℝ)).symm
    _ = Real.rpow (3 : ℝ) ((2 * s) * (j : ℝ)) := by
          congr 1
          ring
    _ = Real.rpow (Real.rpow (3 : ℝ) (2 * s)) (j : ℝ) := by
          simpa using
            (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (2 * s) (j : ℝ))
    _ = (Real.rpow (3 : ℝ) (2 * s)) ^ j := by
          exact Real.rpow_natCast _ j

theorem cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs : s < 0) :
    cubeL2ScalarPartialSeminormTwo Q s N v ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * s))⁻¹) * cubeLpNorm Q (2 : ℝ≥0∞) v := by
  let r : ℝ := Real.rpow (3 : ℝ) (2 * s)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum_bound :
      ∑ j ∈ Finset.range (N + 1), (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 ≤ (1 - r)⁻¹ := by
    calc
      ∑ j ∈ Finset.range (N + 1), (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2
          = ∑ j ∈ Finset.range (N + 1), r ^ j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [rpow_three_weight_sq_eq_geometric_ratio_pow]
      _ ≤ (1 - r)⁻¹ := geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one
  have hsqrt_bound :
      Real.sqrt (∑ j ∈ Finset.range (N + 1), (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2) ≤
        Real.sqrt ((1 - r)⁻¹) := by
    exact Real.sqrt_le_sqrt hsum_bound
  have hpartial_eq :
      cubeL2ScalarPartialSeminormTwo Q s N v =
        cubeLpNorm Q (2 : ℝ≥0∞) v *
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2) := by
    calc
      cubeL2ScalarPartialSeminormTwo Q s N v
          = Real.sqrt (∑ j ∈ Finset.range (N + 1),
              (cubeLpNorm Q (2 : ℝ≥0∞) v * Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2) := by
                unfold cubeL2ScalarPartialSeminormTwo
                refine congrArg Real.sqrt ?_
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [cubeL2ScalarDepthSeminorm_eq_rpow_mul_cubeLpNorm_two Q s v j hv]
                ring
      _ = cubeLpNorm Q (2 : ℝ≥0∞) v *
            Real.sqrt (∑ j ∈ Finset.range (N + 1), (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2) := by
              exact sqrt_sum_sq_const_mul_eq (Finset.range (N + 1))
                (cubeLpNorm Q (2 : ℝ≥0∞) v)
                (fun j => Real.rpow (3 : ℝ) (s * (j : ℝ)))
                (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v)
  have hnorm_nonneg : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) v :=
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v
  calc
    cubeL2ScalarPartialSeminormTwo Q s N v
        = cubeLpNorm Q (2 : ℝ≥0∞) v *
            Real.sqrt (∑ j ∈ Finset.range (N + 1), (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2) := hpartial_eq
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) v * Real.sqrt ((1 - r)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hsqrt_bound hnorm_nonneg
    _ = Real.sqrt ((1 - r)⁻¹) * cubeLpNorm Q (2 : ℝ≥0∞) v := by
          ring

theorem cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_note_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B C : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            cubeLpNorm Q (2 : ℝ≥0∞) u) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := by
  have hraw :=
    cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
      Q s N u ξ hB hu hξLp hξ hderiv
  have hs_neg : s - 1 < 0 := by linarith
  have hL2 :
      cubeL2ScalarPartialSeminormTwo Q (s - 1) N u ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          cubeLpNorm Q (2 : ℝ≥0∞) u := by
    exact cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
      Q (s - 1) N u hu hs_neg
  have hmem :
      ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro j hj R hR
    exact memLp_on_descendant_of_memLp_generic (E := ℝ) hR hu
  have hpos_eq :
      cubeBesovPositiveScalarPartialSeminormTwo Q s N u =
        cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u) := by
    simpa [cubeFluctuation] using!
      (cubeBesovPositiveScalarPartialSeminormTwo_sub_const
        Q s N u (cubeAverage Q u) hmem).symm
  have hfluct :
      cubeBesovPositiveScalarPartialSeminormTwo Q s N u ≤
        cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) *
            cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g) := by
    rw [hpos_eq]
    exact
      hproj.fluctuation_positiveScalarPartialSeminormTwo_le_note_rhs
        (u := u) (hg := hg) hs0 hC
  have hcoeff_nonneg : 0 ≤ cubeScaleFactor Q * B := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hB
  have hterm1 :
      cubeScaleFactor Q * B * cubeL2ScalarPartialSeminormTwo Q (s - 1) N u ≤
        cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            cubeLpNorm Q (2 : ℝ≥0∞) u) := by
    exact mul_le_mul_of_nonneg_left hL2 hcoeff_nonneg
  have hterm2 :
      cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N u ≤
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g)) := by
    exact mul_le_mul_of_nonneg_left hfluct (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x • ξ x)
        ≤ 2 * (cubeScaleFactor Q * B *
            cubeL2ScalarPartialSeminormTwo Q (s - 1) N u +
          cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarPartialSeminormTwo Q s N u) := hraw
    _ ≤ 2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              cubeLpNorm Q (2 : ℝ≥0∞) u) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) *
                cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)

theorem cubeBesovPositiveVectorSeminormTwo_scalar_smul_le_note_poincare_cutoff_terms
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    {B C BcircS : ℝ} (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hnegS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ BcircS) :
    cubeBesovPositiveVectorSeminormTwo Q s (fun x => u x • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            cubeLpNorm Q (2 : ℝ≥0∞) u) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) := by
  refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound (Q := Q) (s := s)
    (u := fun x => u x • ξ x) ?_
  intro N
  have hpartial :=
    cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_note_poincare_cutoff_terms
      Q s N u g ξ hB hu (hproj N) hg hξLp hξ hderiv hs0 hs1 hC
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
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x • ξ x)
        ≤ 2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              cubeLpNorm Q (2 : ℝ≥0∞) u) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) *
                cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g))) := hpartial
    _ ≤ 2 * (cubeScaleFactor Q * B *
            (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
              cubeLpNorm Q (2 : ℝ≥0∞) u) +
          cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight (-s) Q *
              ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                (1 - (3 : ℝ) ^ (-s))⁻¹) * BcircS))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm2) (by norm_num)


end

end Homogenization
