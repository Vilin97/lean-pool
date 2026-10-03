/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QOne

/-! # QTwo -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two
    {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) =
      (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hdisc_ne : geometricDiscount s 2 ≠ 0 := (geometricDiscount_pos hs2).ne'
  calc
    Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) =
        (geometricDiscount s 2)⁻¹ *
          (geometricDiscount s 2 * Real.rpow (3 : ℝ) (-2 * s * (j : ℝ))) := by
            field_simp [hdisc_ne]
    _ = (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
          unfold geometricWeight
          congr 1
          ring_nf

theorem sq_coarsePoincare_gradient_qtwo_partial_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g : Vec d → Vec d) (energy : Vec d → ℝ) (N : ℕ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N g) ^ 2 ≤
      (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹ *
        cubeAverage Q energy := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hdisc_pos : 0 < geometricDiscount s 2 := geometricDiscount_pos hs2
  let coeff : ℕ → ℝ := fun n =>
    geometricWeight s 2 n *
      maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a
  have hdepth_sq :
      ∀ j ∈ Finset.range (N + 1),
        (cubeBesovNegativeVectorDepthSeminorm Q s g j) ^ 2 ≤
          (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy := by
    intro j hj
    have havg :=
      cubeBesovNegativeVectorDepthAverage_le_gradientEnergy
        (Q := Q) a g energy henergy_nonneg henergy_int hgrad j
    have hdepth_nonneg : 0 ≤ cubeBesovNegativeVectorDepthAverage Q g j :=
      cubeBesovNegativeVectorDepthAverage_nonneg Q g j
    have hweight_sq :
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
          (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
      calc
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
            Real.rpow (3 : ℝ) ((-s * (j : ℝ)) * 2) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s * (j : ℝ)) (2 : ℝ)).symm
        _ = Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by ring_nf
        _ = (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
              exact rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two hs j
    calc
      (cubeBesovNegativeVectorDepthSeminorm Q s g j) ^ 2 =
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            cubeBesovNegativeVectorDepthAverage Q g j := by
            unfold cubeBesovNegativeVectorDepthSeminorm
            calc
              (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                  Real.sqrt (cubeBesovNegativeVectorDepthAverage Q g j)) ^ 2
                  =
                    (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                      (Real.sqrt (cubeBesovNegativeVectorDepthAverage Q g j)) ^ 2 := by
                        ring
              _ =
                  (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                    cubeBesovNegativeVectorDepthAverage Q g j := by
                      rw [Real.sq_sqrt hdepth_nonneg]
      _ ≤ (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
              cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_left havg (sq_nonneg _)
      _ = (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy := by
            rw [hweight_sq]
            dsimp [coeff]
            ring
  have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ coeff n := by
    intro n
    dsimp [coeff]
    refine mul_nonneg (geometricWeight_nonneg n (by nlinarith [hs.le])) ?_
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hpartial_sq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N g) ^ 2 ≤
        (geometricDiscount s 2)⁻¹ *
          Finset.sum (Finset.range (N + 1)) coeff *
          cubeAverage Q energy := by
    rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
    calc
      Finset.sum (Finset.range (N + 1)) (fun j =>
          (cubeBesovNegativeVectorDepthSeminorm Q s g j) ^ 2)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
            (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy) := by
              exact Finset.sum_le_sum hdepth_sq
      _ = (geometricDiscount s 2)⁻¹ *
            Finset.sum (Finset.range (N + 1)) coeff *
            cubeAverage Q energy := by
            calc
              Finset.sum (Finset.range (N + 1)) (fun j =>
                  (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy)
                  =
                    Finset.sum (Finset.range (N + 1)) (fun j =>
                      ((geometricDiscount s 2)⁻¹ * cubeAverage Q energy) * coeff j) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        ring
              _ = ((geometricDiscount s 2)⁻¹ * cubeAverage Q energy) *
                    Finset.sum (Finset.range (N + 1)) coeff := by
                      rw [Finset.mul_sum]
              _ = (geometricDiscount s 2)⁻¹ *
                    Finset.sum (Finset.range (N + 1)) coeff *
                    cubeAverage Q energy := by
                      ring
  have hfinite_le_tsum :
      Finset.sum (Finset.range (N + 1)) coeff ≤ ∑' n : ℕ, coeff n := by
    exact hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hcoeff_nonneg n)
  have hcoeff_tsum :
      ∑' n : ℕ, coeff n = (lambdaSq Q s (.finite 2) a)⁻¹ := by
    dsimp [coeff]
    calc
      ∑' n : ℕ,
          geometricWeight s 2 n *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a
          = Real.rpow (lambdaSq Q s (.finite 2) a) (-1 : ℝ) := by
              simpa using
                (multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum
                  Q s (2 : ℝ) a (by norm_num) (by nlinarith [hs])).symm
      _ = (lambdaSq Q s (.finite 2) a)⁻¹ := by
            exact Real.rpow_neg_one (lambdaSq Q s (.finite 2) a)
  calc
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N g) ^ 2
        ≤ (geometricDiscount s 2)⁻¹ *
            Finset.sum (Finset.range (N + 1)) coeff *
            cubeAverage Q energy := hpartial_sq
    _ ≤ (geometricDiscount s 2)⁻¹ * (∑' n : ℕ, coeff n) * cubeAverage Q energy := by
          have hscaled :
              (geometricDiscount s 2)⁻¹ * Finset.sum (Finset.range (N + 1)) coeff ≤
                (geometricDiscount s 2)⁻¹ * ∑' n : ℕ, coeff n := by
            exact mul_le_mul_of_nonneg_left hfinite_le_tsum
              (inv_nonneg.mpr hdisc_pos.le)
          exact mul_le_mul_of_nonneg_right hscaled henergy_avg_nonneg
    _ = (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹ *
          cubeAverage Q energy := by
          rw [hcoeff_tsum]

theorem coarsePoincare_gradient_qtwo_partial_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g : Vec d → Vec d) (energy : Vec d → ℝ) (N : ℕ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N g ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  let B : ℝ :=
    Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
      Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) *
      Real.sqrt (cubeAverage Q energy)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg (mul_nonneg ?_ ?_) (Real.sqrt_nonneg _)
    · exact Real.rpow_nonneg (geometricDiscount_nonneg (by nlinarith [hs.le])) _
    · exact Real.rpow_nonneg hlambda_nonneg _
  have hB_sq :
      B ^ 2 =
        (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹ *
          cubeAverage Q energy := by
    dsimp [B]
    calc
      (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy)) ^ 2
          =
            (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 *
              (Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ)) ^ 2 *
              (Real.sqrt (cubeAverage Q energy)) ^ 2 := by
                ring
      _ = (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹ *
            cubeAverage Q energy := by
              rw [sq_rpow_neg_half_eq_inv_of_nonneg
                    (geometricDiscount_nonneg (by nlinarith [hs.le])),
                sq_rpow_neg_half_eq_inv_of_nonneg hlambda_nonneg,
                Real.sq_sqrt henergy_avg_nonneg]
  have hsq :=
    sq_coarsePoincare_gradient_qtwo_partial_of_cubeAverageEnergyControl
      Q a s hs g energy N henergy_nonneg henergy_int hgrad hsum
  rw [← hB_sq] at hsq
  have hpartial_nonneg := cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N g
  have habs : |cubeBesovNegativeVectorPartialSeminormTwo Q s N g| ≤ |B| := by
    exact sq_le_sq.mp hsq
  simpa [abs_of_nonneg hpartial_nonneg, abs_of_nonneg hB_nonneg] using! habs

/-- Note-facing `q = 2` gradient coarse Poincare inequality under descendant
cube-average energy control. -/
theorem coarsePoincare_gradient_qtwo_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    cubeBesovNegativeVectorSeminormTwo Q s g ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  exact cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s g <|
    coarsePoincare_gradient_qtwo_partial_of_cubeAverageEnergyControl
      Q a s hs g energy
      (henergy_nonneg := henergy_nonneg)
      (henergy_int := henergy_int)
      (hgrad := hgrad)
      (hsum := hsum)

/-- Squared finite-depth `q = 2` flux coarse Poincare inequality under
descendant cube-average energy control. -/
theorem sq_coarsePoincare_flux_qtwo_partial_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (flux : Vec d → Vec d) (energy : Vec d → ℝ) (N : ℕ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N flux) ^ 2 ≤
      (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
        cubeAverage Q energy := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hdisc_pos : 0 < geometricDiscount s 2 := geometricDiscount_pos hs2
  let coeff : ℕ → ℝ := fun n =>
    geometricWeight s 2 n *
      maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a
  have hdepth_sq :
      ∀ j ∈ Finset.range (N + 1),
        (cubeBesovNegativeVectorDepthSeminorm Q s flux j) ^ 2 ≤
          (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy := by
    intro j hj
    have havg :=
      cubeBesovNegativeVectorDepthAverage_le_fluxEnergy
        (Q := Q) a flux energy henergy_nonneg henergy_int hflux j
    have hdepth_nonneg : 0 ≤ cubeBesovNegativeVectorDepthAverage Q flux j :=
      cubeBesovNegativeVectorDepthAverage_nonneg Q flux j
    have hweight_sq :
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
          (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
      calc
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
            Real.rpow (3 : ℝ) ((-s * (j : ℝ)) * 2) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s * (j : ℝ)) (2 : ℝ)).symm
        _ = Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by ring_nf
        _ = (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
              exact rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two hs j
    calc
      (cubeBesovNegativeVectorDepthSeminorm Q s flux j) ^ 2 =
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            cubeBesovNegativeVectorDepthAverage Q flux j := by
            unfold cubeBesovNegativeVectorDepthSeminorm
            calc
              (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                  Real.sqrt (cubeBesovNegativeVectorDepthAverage Q flux j)) ^ 2
                  =
                    (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                      (Real.sqrt (cubeBesovNegativeVectorDepthAverage Q flux j)) ^ 2 := by
                        ring
              _ =
                  (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                    cubeBesovNegativeVectorDepthAverage Q flux j := by
                      rw [Real.sq_sqrt hdepth_nonneg]
      _ ≤ (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
              cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_left havg (sq_nonneg _)
      _ = (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy := by
            rw [hweight_sq]
            dsimp [coeff]
            ring
  have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ coeff n := by
    intro n
    dsimp [coeff]
    refine mul_nonneg (geometricWeight_nonneg n (by nlinarith [hs.le])) ?_
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hpartial_sq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N flux) ^ 2 ≤
        (geometricDiscount s 2)⁻¹ *
          Finset.sum (Finset.range (N + 1)) coeff *
          cubeAverage Q energy := by
    rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
    calc
      Finset.sum (Finset.range (N + 1)) (fun j =>
          (cubeBesovNegativeVectorDepthSeminorm Q s flux j) ^ 2)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
            (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy) := by
              exact Finset.sum_le_sum hdepth_sq
      _ = (geometricDiscount s 2)⁻¹ *
            Finset.sum (Finset.range (N + 1)) coeff *
            cubeAverage Q energy := by
            calc
              Finset.sum (Finset.range (N + 1)) (fun j =>
                  (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy)
                  =
                    Finset.sum (Finset.range (N + 1)) (fun j =>
                      ((geometricDiscount s 2)⁻¹ * cubeAverage Q energy) * coeff j) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        ring
              _ = ((geometricDiscount s 2)⁻¹ * cubeAverage Q energy) *
                    Finset.sum (Finset.range (N + 1)) coeff := by
                      rw [Finset.mul_sum]
              _ = (geometricDiscount s 2)⁻¹ *
                    Finset.sum (Finset.range (N + 1)) coeff *
                    cubeAverage Q energy := by
                      ring
  have hfinite_le_tsum :
      Finset.sum (Finset.range (N + 1)) coeff ≤ ∑' n : ℕ, coeff n := by
    exact hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hcoeff_nonneg n)
  have hcoeff_tsum :
      ∑' n : ℕ, coeff n = LambdaSq Q s (.finite 2) a := by
    dsimp [coeff]
    calc
      ∑' n : ℕ,
          geometricWeight s 2 n *
            maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a
          = Real.rpow (LambdaSq Q s (.finite 2) a) (1 : ℝ) := by
              simpa using
                (multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum
                  Q s (2 : ℝ) a (by norm_num) (by nlinarith [hs])).symm
      _ = LambdaSq Q s (.finite 2) a := by
            exact Real.rpow_one (LambdaSq Q s (.finite 2) a)
  calc
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N flux) ^ 2
        ≤ (geometricDiscount s 2)⁻¹ *
            Finset.sum (Finset.range (N + 1)) coeff *
            cubeAverage Q energy := hpartial_sq
    _ ≤ (geometricDiscount s 2)⁻¹ * (∑' n : ℕ, coeff n) *
          cubeAverage Q energy := by
        have hscaled :
            (geometricDiscount s 2)⁻¹ * Finset.sum (Finset.range (N + 1)) coeff ≤
              (geometricDiscount s 2)⁻¹ * ∑' n : ℕ, coeff n := by
          exact mul_le_mul_of_nonneg_left hfinite_le_tsum
            (inv_nonneg.mpr hdisc_pos.le)
        exact mul_le_mul_of_nonneg_right hscaled henergy_avg_nonneg
    _ = (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
        cubeAverage Q energy := by
        rw [hcoeff_tsum]

/-- Note-facing `q = 2` finite-depth flux coarse Poincare inequality under
descendant cube-average energy control. -/
theorem coarsePoincare_flux_qtwo_partial_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (flux : Vec d → Vec d) (energy : Vec d → ℝ) (N : ℕ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N flux ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  let B : ℝ :=
    Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
      Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
      Real.sqrt (cubeAverage Q energy)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg (mul_nonneg ?_ ?_) (Real.sqrt_nonneg _)
    · exact Real.rpow_nonneg (geometricDiscount_nonneg (by nlinarith [hs.le])) _
    · exact Real.rpow_nonneg hLambda_nonneg _
  have hB_sq :
      B ^ 2 =
        (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
          cubeAverage Q energy := by
    dsimp [B]
    calc
      (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
          Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy)) ^ 2
          =
            (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 *
              (Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ)) ^ 2 *
              (Real.sqrt (cubeAverage Q energy)) ^ 2 := by
                ring
      _ = (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
            cubeAverage Q energy := by
              rw [sq_rpow_neg_half_eq_inv_of_nonneg
                    (geometricDiscount_nonneg (by nlinarith [hs.le])),
                sq_rpow_half_eq_self_of_nonneg hLambda_nonneg,
                Real.sq_sqrt henergy_avg_nonneg]
  have hsq :=
    sq_coarsePoincare_flux_qtwo_partial_of_cubeAverageEnergyControl
      Q a s hs flux energy N henergy_nonneg henergy_int hflux hsum
  rw [← hB_sq] at hsq
  have hpartial_nonneg := cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N flux
  have habs : |cubeBesovNegativeVectorPartialSeminormTwo Q s N flux| ≤ |B| := by
    exact sq_le_sq.mp hsq
  change cubeBesovNegativeVectorPartialSeminormTwo Q s N flux ≤ B
  simpa [abs_of_nonneg hpartial_nonneg, abs_of_nonneg hB_nonneg] using habs

/-- Note-facing `q = 2` flux coarse Poincare inequality under descendant
cube-average energy control. -/
theorem coarsePoincare_flux_qtwo_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    cubeBesovNegativeVectorSeminormTwo Q s flux ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hdisc_pos : 0 < geometricDiscount s 2 := geometricDiscount_pos hs2
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  let B : ℝ :=
    Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
      Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
      Real.sqrt (cubeAverage Q energy)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg (mul_nonneg ?_ ?_) (Real.sqrt_nonneg _)
    · exact Real.rpow_nonneg (geometricDiscount_nonneg (by nlinarith [hs.le])) _
    · exact Real.rpow_nonneg hLambda_nonneg _
  have hB_sq :
      B ^ 2 =
        (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
          cubeAverage Q energy := by
    dsimp [B]
    calc
      (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
          Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy)) ^ 2
          =
            (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 *
              (Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ)) ^ 2 *
              (Real.sqrt (cubeAverage Q energy)) ^ 2 := by
                ring
      _ = (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
            cubeAverage Q energy := by
              rw [sq_rpow_neg_half_eq_inv_of_nonneg
                    (geometricDiscount_nonneg (by nlinarith [hs.le])),
                sq_rpow_half_eq_self_of_nonneg hLambda_nonneg,
                Real.sq_sqrt henergy_avg_nonneg]
  have hpartial :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N flux ≤ B := by
    intro N
    let coeff : ℕ → ℝ := fun n =>
      geometricWeight s 2 n *
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a
    have hdepth_sq :
        ∀ j ∈ Finset.range (N + 1),
          (cubeBesovNegativeVectorDepthSeminorm Q s flux j) ^ 2 ≤
            (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy := by
      intro j hj
      have havg :=
        cubeBesovNegativeVectorDepthAverage_le_fluxEnergy
          (Q := Q) a flux energy henergy_nonneg henergy_int hflux j
      have hdepth_nonneg : 0 ≤ cubeBesovNegativeVectorDepthAverage Q flux j :=
        cubeBesovNegativeVectorDepthAverage_nonneg Q flux j
      have hmax_nonneg :
          0 ≤ maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a := by
        exact maxDescendantBBlockNormAtScale_nonneg Q
          (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) a
      have hweight_sq :
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
            (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
        calc
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
              Real.rpow (3 : ℝ) ((-s * (j : ℝ)) * 2) := by
                simpa [Real.rpow_natCast] using
                  (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s * (j : ℝ)) (2 : ℝ)).symm
          _ = Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by ring_nf
          _ = (geometricDiscount s 2)⁻¹ * geometricWeight s 2 j := by
                exact rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two hs j
      calc
        (cubeBesovNegativeVectorDepthSeminorm Q s flux j) ^ 2 =
            (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              cubeBesovNegativeVectorDepthAverage Q flux j := by
              unfold cubeBesovNegativeVectorDepthSeminorm
              calc
                (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                    Real.sqrt (cubeBesovNegativeVectorDepthAverage Q flux j)) ^ 2
                    =
                      (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                        (Real.sqrt (cubeBesovNegativeVectorDepthAverage Q flux j)) ^ 2 := by
                          ring
                _ =
                    (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                      cubeBesovNegativeVectorDepthAverage Q flux j := by
                        rw [Real.sq_sqrt hdepth_nonneg]
        _ ≤ (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              (maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
                cubeAverage Q energy) := by
              exact mul_le_mul_of_nonneg_left havg (sq_nonneg _)
        _ = (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy := by
              rw [hweight_sq]
              dsimp [coeff]
              ring
    have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ coeff n := by
      intro n
      dsimp [coeff]
      refine mul_nonneg (geometricWeight_nonneg n (by nlinarith [hs.le])) ?_
      exact maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
    have hpartial_sq :
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N flux) ^ 2 ≤
          (geometricDiscount s 2)⁻¹ *
            Finset.sum (Finset.range (N + 1)) coeff *
            cubeAverage Q energy := by
      rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
      calc
        Finset.sum (Finset.range (N + 1)) (fun j =>
            (cubeBesovNegativeVectorDepthSeminorm Q s flux j) ^ 2)
            ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
              (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy) := by
                exact Finset.sum_le_sum hdepth_sq
        _ = (geometricDiscount s 2)⁻¹ *
              Finset.sum (Finset.range (N + 1)) coeff *
              cubeAverage Q energy := by
              calc
                Finset.sum (Finset.range (N + 1)) (fun j =>
                    (geometricDiscount s 2)⁻¹ * coeff j * cubeAverage Q energy)
                    =
                      Finset.sum (Finset.range (N + 1)) (fun j =>
                        ((geometricDiscount s 2)⁻¹ * cubeAverage Q energy) * coeff j) := by
                          refine Finset.sum_congr rfl ?_
                          intro j hj
                          ring
                _ = ((geometricDiscount s 2)⁻¹ * cubeAverage Q energy) *
                      Finset.sum (Finset.range (N + 1)) coeff := by
                        rw [Finset.mul_sum]
                _ = (geometricDiscount s 2)⁻¹ *
                      Finset.sum (Finset.range (N + 1)) coeff *
                      cubeAverage Q energy := by
                        ring
    have hfinite_le_tsum :
        Finset.sum (Finset.range (N + 1)) coeff ≤ ∑' n : ℕ, coeff n := by
      exact hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hcoeff_nonneg n)
    have hcoeff_tsum :
        ∑' n : ℕ, coeff n = LambdaSq Q s (.finite 2) a := by
      dsimp [coeff]
      calc
        ∑' n : ℕ,
            geometricWeight s 2 n *
              maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a
            = Real.rpow (LambdaSq Q s (.finite 2) a) (1 : ℝ) := by
                simpa using
                  (multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum
                    Q s (2 : ℝ) a (by norm_num) (by nlinarith [hs])).symm
        _ = LambdaSq Q s (.finite 2) a := by
              exact Real.rpow_one (LambdaSq Q s (.finite 2) a)
    have hbound_sq :
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N flux) ^ 2 ≤
          (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
            cubeAverage Q energy := by
      calc
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N flux) ^ 2
            ≤ (geometricDiscount s 2)⁻¹ *
                Finset.sum (Finset.range (N + 1)) coeff *
                cubeAverage Q energy := hpartial_sq
        _ ≤ (geometricDiscount s 2)⁻¹ * (∑' n : ℕ, coeff n) * cubeAverage Q energy := by
              have hscaled :
                  (geometricDiscount s 2)⁻¹ * Finset.sum (Finset.range (N + 1)) coeff ≤
                    (geometricDiscount s 2)⁻¹ * ∑' n : ℕ, coeff n := by
                exact mul_le_mul_of_nonneg_left hfinite_le_tsum
                  (inv_nonneg.mpr hdisc_pos.le)
              exact mul_le_mul_of_nonneg_right hscaled henergy_avg_nonneg
        _ = (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
              cubeAverage Q energy := by
              rw [hcoeff_tsum]
    rw [← hB_sq] at hbound_sq
    have hpartial_nonneg := cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N flux
    have habs : |cubeBesovNegativeVectorPartialSeminormTwo Q s N flux| ≤ |B| := by
      exact sq_le_sq.mp hbound_sq
    simpa [abs_of_nonneg hpartial_nonneg, abs_of_nonneg hB_nonneg] using habs
  exact cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s flux hpartial

/-- Note-facing `q = 2` gradient and flux coarse Poincare bounds under direct
descendant cube-average energy control. -/
theorem coarsePoincare_qtwo_note_bounds_of_cubeAverageEnergyControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum_grad :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (hsum_flux :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)) :
    cubeBesovNegativeVectorSeminormTwo Q s g ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) ∧
    cubeBesovNegativeVectorSeminormTwo Q s flux ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  refine ⟨?_, ?_⟩
  · exact
      coarsePoincare_gradient_qtwo_of_cubeAverageEnergyControl
        (Q := Q) (a := a) (s := s) hs (g := g) (energy := energy)
        henergy_nonneg henergy_int hgrad hsum_grad
  · exact
      coarsePoincare_flux_qtwo_of_cubeAverageEnergyControl
        (Q := Q) (a := a) (s := s) hs (flux := flux) (energy := energy)
        henergy_nonneg henergy_int hflux hsum_flux


/-- Note-facing `q = 2` gradient and flux coarse Poincare bounds for one
harmonic field on the parent cube. -/
theorem coarsePoincare_qtwo_note_bounds_of_aHarmonicFunction
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => u.toH1.grad x) ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a u x)) ∧
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => matVecMul (a x) (u.toH1.grad x)) ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a u x)) := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hsum_grad :=
    summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) s hs hEll hOrigin
  have hsum_flux :=
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) s hs hEll hOrigin
  exact
    coarsePoincare_qtwo_note_bounds_of_cubeAverageEnergyControl
      (Q := Q) (a := a) (s := s) hs
      (g := fun x => u.toH1.grad x)
      (flux := fun x => matVecMul (a x) (u.toH1.grad x))
      (energy := fun x => scalarVariationEnergyIntegrand a u x)
      (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) a hEll u)
      (ResponseLinearIntegrabilityData.energy
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u)
      (cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEll u hOrigin)
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEll u hOrigin)
      hsum_grad hsum_flux


end

end Homogenization
