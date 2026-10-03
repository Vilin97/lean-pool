/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QOne

/-! # Flux -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Energy bridges for coarse Caccioppoli

This sidecar file connects the local cutoff-product Caccioppoli estimate to the
coarse-Poincare energy-control surface, without editing the active Poincare
files.  The main point is to expose the finite `q = 1` flux partial bounds that
the local pairing theorem consumes.
-/

theorem norm_le_sqrt_vecNormSq {d : ℕ} (v : Vec d) :
    ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
  intro i
  have hsq : ‖v i‖ ^ (2 : ℕ) ≤ (Real.sqrt (vecNormSq v)) ^ (2 : ℕ) := by
    calc
      ‖v i‖ ^ (2 : ℕ) = v i ^ (2 : ℕ) := by
        rw [Real.norm_eq_abs, sq_abs]
      _ ≤ vecNormSq v := sq_apply_le_vecNormSq v i
      _ = (Real.sqrt (vecNormSq v)) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt (vecNormSq_nonneg v)]
  exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)

theorem norm_cubeAverageVec_le_sqrt_coarseBBlockNorm_mul_cubeAverage_of_fluxEnergyControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy) :
    ‖cubeAverageVec Q flux‖ ≤
      Real.sqrt (coarseBBlockNorm Q a * cubeAverage Q energy) := by
  have hQ : Q ∈ descendantsAtDepth Q 0 := by
    simp [descendantsAtDepth_zero]
  have hsq :
      vecNormSq (cubeAverageVec Q flux) ≤
        coarseBBlockNorm Q a * cubeAverage Q energy := hflux 0 Q hQ
  calc
    ‖cubeAverageVec Q flux‖
        ≤ Real.sqrt (vecNormSq (cubeAverageVec Q flux)) :=
          norm_le_sqrt_vecNormSq (cubeAverageVec Q flux)
    _ ≤ Real.sqrt (coarseBBlockNorm Q a * cubeAverage Q energy) :=
          Real.sqrt_le_sqrt hsq

theorem norm_cubeAverageVec_le_sqrt_coarseBBlockNorm_mul_sqrt_cubeAverage_of_fluxEnergyControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy) :
    ‖cubeAverageVec Q flux‖ ≤
      Real.sqrt (coarseBBlockNorm Q a) * Real.sqrt (cubeAverage Q energy) := by
  calc
    ‖cubeAverageVec Q flux‖
        ≤ Real.sqrt (coarseBBlockNorm Q a * cubeAverage Q energy) :=
          norm_cubeAverageVec_le_sqrt_coarseBBlockNorm_mul_cubeAverage_of_fluxEnergyControl
            Q a flux energy hflux
    _ = Real.sqrt (coarseBBlockNorm Q a) * Real.sqrt (cubeAverage Q energy) := by
          rw [Real.sqrt_mul (coarseBBlockNorm_nonneg Q a)]

theorem sqrt_coarseBBlockNorm_le_inv_geometricDiscount_mul_LambdaSq_one_rpow_half
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (hs : 0 < s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.sqrt (coarseBBlockNorm Q a) ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hbase :
      geometricDiscount s 1 * Real.sqrt (coarseBBlockNorm Q a) ≤
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using
      geometricDiscount_mul_sqrt_coarseBBlockNorm_le_LambdaSq_one_rpow_half
        Q a s hs.le hsum
  calc
    Real.sqrt (coarseBBlockNorm Q a)
        = (geometricDiscount s 1)⁻¹ *
            (geometricDiscount s 1 * Real.sqrt (coarseBBlockNorm Q a)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hdisc_pos.ne', one_mul]
    _ ≤ (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hdisc_pos.le)

/-- Canonical `q = 1` coefficient factor used by the Caccioppoli local bridge.
It simultaneously bounds the block-average coefficient and the negative Besov
flux coefficient once the corresponding geometric series is summable. -/
noncomputable def coarseCaccioppoliLambdaFactor {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s : ℝ) : ℝ :=
  (geometricDiscount s 1)⁻¹ *
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)

theorem coarseCaccioppoliLambdaFactor_nonneg {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ coarseCaccioppoliLambdaFactor Q a s := by
  unfold coarseCaccioppoliLambdaFactor
  have hdisc_nonneg : 0 ≤ (geometricDiscount s 1)⁻¹ := by
    by_cases hs0 : 0 < s
    · exact inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs0)).le
    · exact inv_nonneg.mpr (geometricDiscount_nonneg (by simpa using hs))
  exact mul_nonneg hdisc_nonneg
    (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs) _)

theorem sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (hs : 0 < s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.sqrt (coarseBBlockNorm Q a) ≤ coarseCaccioppoliLambdaFactor Q a s := by
  simpa [coarseCaccioppoliLambdaFactor] using
    sqrt_coarseBBlockNorm_le_inv_geometricDiscount_mul_LambdaSq_one_rpow_half
      Q a hs hsum

/-- Finite `q = 1` gradient coarse-Poincare bound, exposed in the Caccioppoli
bridge namespace so scalar component `circ` bounds can be built without
reopening the active Poincare files. -/
theorem coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g : Vec d → Vec d) (energy : Vec d → ℝ) (N : ℕ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    cubeBesovNegativeVectorPartialSeminorm Q s N g ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos hs1
  let coeff : ℕ → ℝ := fun n =>
    Real.rpow (3 : ℝ) (-s * (n : ℝ)) *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2 : ℝ)
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovNegativeVectorDepthSeminorm Q s g j ≤
          coeff j * Real.sqrt (cubeAverage Q energy) := by
    intro j hj
    have havg :=
      cubeBesovNegativeVectorDepthAverage_le_gradientEnergy
        (Q := Q) a g energy henergy_nonneg henergy_int hgrad j
    have hmax_nonneg :
        0 ≤ maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a := by
      exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) a
    have hsqrt :
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q g j) ≤
          Real.sqrt
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
              cubeAverage Q energy) := by
      exact Real.sqrt_le_sqrt havg
    calc
      cubeBesovNegativeVectorDepthSeminorm Q s g j =
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (cubeBesovNegativeVectorDepthAverage Q g j) := by
            rfl
      _ ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt
              (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
                cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_left hsqrt
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ = coeff j * Real.sqrt (cubeAverage Q energy) := by
            unfold coeff
            rw [mul_sqrt_mul_eq_mul_rpow_half_mul_sqrt hmax_nonneg]
  have hsum_partial :
      cubeBesovNegativeVectorPartialSeminorm Q s N g ≤
        Finset.sum (Finset.range (N + 1)) coeff * Real.sqrt (cubeAverage Q energy) := by
    unfold cubeBesovNegativeVectorPartialSeminorm
    calc
      Finset.sum (Finset.range (N + 1)) (fun j =>
          cubeBesovNegativeVectorDepthSeminorm Q s g j)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
            coeff j * Real.sqrt (cubeAverage Q energy)) := by
              exact Finset.sum_le_sum hdepth
      _ = Finset.sum (Finset.range (N + 1)) coeff * Real.sqrt (cubeAverage Q energy) := by
            rw [Finset.sum_mul]
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) ?_
    exact Real.rpow_nonneg
      (maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a) _
  have hcoeff_eq :
      Finset.sum (Finset.range (N + 1)) coeff =
        (geometricDiscount s 1)⁻¹ *
          Finset.sum (Finset.range (N + 1)) (fun j =>
            geometricWeight s 1 j *
              Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a)
                (1 / 2 : ℝ)) := by
    unfold coeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [rpow_neg_s_nat_eq_inv_geometricDiscount_mul_geometricWeight hs j]
    ring
  have hfinite_le_tsum :
      Finset.sum (Finset.range (N + 1)) (fun j =>
          geometricWeight s 1 j *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a)
              (1 / 2 : ℝ))
        ≤ ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
    exact hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hcoeff_nonneg n)
  calc
    cubeBesovNegativeVectorPartialSeminorm Q s N g
        ≤ Finset.sum (Finset.range (N + 1)) coeff * Real.sqrt (cubeAverage Q energy) :=
          hsum_partial
    _ = (geometricDiscount s 1)⁻¹ *
          Finset.sum (Finset.range (N + 1)) (fun j =>
            geometricWeight s 1 j *
              Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a)
                (1 / 2 : ℝ)) *
          Real.sqrt (cubeAverage Q energy) := by
            rw [hcoeff_eq]
    _ ≤ (geometricDiscount s 1)⁻¹ *
          (∑' n : ℕ,
            geometricWeight s 1 n *
              Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) *
          Real.sqrt (cubeAverage Q energy) := by
            have hscaled :
                (geometricDiscount s 1)⁻¹ *
                    Finset.sum (Finset.range (N + 1)) (fun j =>
                      geometricWeight s 1 j *
                        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q
                          (Q.scale - (j : ℤ)) a) (1 / 2 : ℝ))
                  ≤
                (geometricDiscount s 1)⁻¹ *
                    (∑' n : ℕ,
                      geometricWeight s 1 n *
                        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q
                          (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hfinite_le_tsum
                (inv_nonneg.mpr hdisc_pos.le)
            exact mul_le_mul_of_nonneg_right hscaled (Real.sqrt_nonneg _)
    _ = (geometricDiscount s 1)⁻¹ *
          Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy) := by
            rw [multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum Q s a hs.le]

/-- Finite `q = 1` flux coarse-Poincare bound, exposed in the Caccioppoli
bridge namespace so the local pairing theorem can consume the exact partial
seminorm hypotheses it needs. -/
theorem coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (flux : Vec d → Vec d) (energy : Vec d → ℝ) (N : ℕ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos hs1
  let coeff : ℕ → ℝ := fun n =>
    Real.rpow (3 : ℝ) (-s * (n : ℝ)) *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2 : ℝ)
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovNegativeVectorDepthSeminorm Q s flux j ≤
          coeff j * Real.sqrt (cubeAverage Q energy) := by
    intro j hj
    have havg :=
      cubeBesovNegativeVectorDepthAverage_le_fluxEnergy
        (Q := Q) a flux energy henergy_nonneg henergy_int hflux j
    have hmax_nonneg :
        0 ≤ maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a := by
      exact maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) a
    have hsqrt :
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q flux j) ≤
          Real.sqrt
            (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
              cubeAverage Q energy) := by
      exact Real.sqrt_le_sqrt havg
    calc
      cubeBesovNegativeVectorDepthSeminorm Q s flux j =
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (cubeBesovNegativeVectorDepthAverage Q flux j) := by
            rfl
      _ ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt
              (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
                cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_left hsqrt
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ = coeff j * Real.sqrt (cubeAverage Q energy) := by
            unfold coeff
            rw [mul_sqrt_mul_eq_mul_rpow_half_mul_sqrt hmax_nonneg]
  have hsum_partial :
      cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤
        Finset.sum (Finset.range (N + 1)) coeff * Real.sqrt (cubeAverage Q energy) := by
    unfold cubeBesovNegativeVectorPartialSeminorm
    calc
      Finset.sum (Finset.range (N + 1)) (fun j =>
          cubeBesovNegativeVectorDepthSeminorm Q s flux j)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
            coeff j * Real.sqrt (cubeAverage Q energy)) := by
              exact Finset.sum_le_sum hdepth
      _ = Finset.sum (Finset.range (N + 1)) coeff * Real.sqrt (cubeAverage Q energy) := by
            rw [Finset.sum_mul]
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) ?_
    exact Real.rpow_nonneg
      (maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a) _
  have hcoeff_eq :
      Finset.sum (Finset.range (N + 1)) coeff =
        (geometricDiscount s 1)⁻¹ *
          Finset.sum (Finset.range (N + 1)) (fun j =>
            geometricWeight s 1 j *
              Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a)
                (1 / 2 : ℝ)) := by
    unfold coeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [rpow_neg_s_nat_eq_inv_geometricDiscount_mul_geometricWeight hs j]
    ring
  have hfinite_le_tsum :
      Finset.sum (Finset.range (N + 1)) (fun j =>
          geometricWeight s 1 j *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a)
              (1 / 2 : ℝ))
        ≤ ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
    exact hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hcoeff_nonneg n)
  calc
    cubeBesovNegativeVectorPartialSeminorm Q s N flux
        ≤ Finset.sum (Finset.range (N + 1)) coeff * Real.sqrt (cubeAverage Q energy) :=
          hsum_partial
    _ = (geometricDiscount s 1)⁻¹ *
          Finset.sum (Finset.range (N + 1)) (fun j =>
            geometricWeight s 1 j *
              Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a)
                (1 / 2 : ℝ)) *
          Real.sqrt (cubeAverage Q energy) := by
            rw [hcoeff_eq]
    _ ≤ (geometricDiscount s 1)⁻¹ *
          (∑' n : ℕ,
            geometricWeight s 1 n *
              Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) *
          Real.sqrt (cubeAverage Q energy) := by
            have hscaled :
                (geometricDiscount s 1)⁻¹ *
                    Finset.sum (Finset.range (N + 1)) (fun j =>
                      geometricWeight s 1 j *
                        Real.rpow (maxDescendantBBlockNormAtScale Q
                          (Q.scale - (j : ℤ)) a) (1 / 2 : ℝ))
                  ≤
                (geometricDiscount s 1)⁻¹ *
                    (∑' n : ℕ,
                      geometricWeight s 1 n *
                        Real.rpow (maxDescendantBBlockNormAtScale Q
                          (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hfinite_le_tsum
                (inv_nonneg.mpr hdisc_pos.le)
            exact mul_le_mul_of_nonneg_right hscaled (Real.sqrt_nonneg _)
    _ = (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy) := by
            rw [multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum Q s a hs.le]

end

end Homogenization
