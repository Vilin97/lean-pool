/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup

/-! # QOne -/

namespace Homogenization

noncomputable section

theorem cubeBesovNegativeVectorDepthAverage_le_gradientEnergy {d : ℕ}
    {Q : TriadicCube d} (a : CoeffField d) (g : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q g j ≤
      maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
        cubeAverage Q energy := by
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R g) ≤
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have havg_nonneg : 0 ≤ cubeAverage R energy := by
      apply cubeAverage_nonneg_of_nonneg_on
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    exact le_trans (hgrad j R hR) <|
      mul_le_mul_of_nonneg_right
        (coarseSigmaStarInvBlockNorm_le_maxDescendantSigmaStarInvNormAtScale a hRscale)
        havg_nonneg
  have hdesc :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  have hconst :
      descendantsAverage Q j (fun R =>
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy) =
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a *
          descendantsAverage Q j (fun R => cubeAverage R energy) := by
    let D := descendantsAtDepth Q j
    let M := maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (j : ℤ)) a
    unfold descendantsAverage
    calc
      ((D.card : ℝ)⁻¹) * Finset.sum D (fun R => M * cubeAverage R energy) =
          Finset.sum D (fun R => (((D.card : ℝ)⁻¹ * M) * cubeAverage R energy)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro R hR
            ring
      _ = (((D.card : ℝ)⁻¹ * M) * Finset.sum D (fun R => cubeAverage R energy)) := by
            simpa [mul_assoc] using
              (Finset.mul_sum (s := D) (f := fun R => cubeAverage R energy)
                (((D.card : ℝ)⁻¹) * M)).symm
      _ = M * (((D.card : ℝ)⁻¹) * Finset.sum D (fun R => cubeAverage R energy)) := by
            ring
  rw [hconst, havg_eq] at hdesc
  simpa [cubeBesovNegativeVectorDepthAverage] using hdesc

theorem cubeBesovNegativeVectorDepthAverage_le_fluxEnergy {d : ℕ}
    {Q : TriadicCube d} (a : CoeffField d) (flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q flux j ≤
      maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
        cubeAverage Q energy := by
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R flux) ≤
          maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have havg_nonneg : 0 ≤ cubeAverage R energy := by
      apply cubeAverage_nonneg_of_nonneg_on
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    exact le_trans (hflux j R hR) <|
      mul_le_mul_of_nonneg_right
        (coarseBBlockNorm_le_maxDescendantBBlockNormAtScale a hRscale)
        havg_nonneg
  have hdesc :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  have hconst :
      descendantsAverage Q j (fun R =>
          maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
            cubeAverage R energy) =
        maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a *
          descendantsAverage Q j (fun R => cubeAverage R energy) := by
    let D := descendantsAtDepth Q j
    let M := maxDescendantBBlockNormAtScale Q (Q.scale - (j : ℤ)) a
    unfold descendantsAverage
    calc
      ((D.card : ℝ)⁻¹) * Finset.sum D (fun R => M * cubeAverage R energy) =
          Finset.sum D (fun R => (((D.card : ℝ)⁻¹ * M) * cubeAverage R energy)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro R hR
            ring
      _ = (((D.card : ℝ)⁻¹ * M) * Finset.sum D (fun R => cubeAverage R energy)) := by
            simpa [mul_assoc] using
              (Finset.mul_sum (s := D) (f := fun R => cubeAverage R energy)
                (((D.card : ℝ)⁻¹) * M)).symm
      _ = M * (((D.card : ℝ)⁻¹) * Finset.sum D (fun R => cubeAverage R energy)) := by
            ring
  rw [hconst, havg_eq] at hdesc
  simpa [cubeBesovNegativeVectorDepthAverage] using hdesc

theorem coarsePoincare_gradient_qone_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    cubeBesovNegativeVectorSeminorm Q s g ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos hs1
  have hpartial :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N g ≤
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) *
            Real.sqrt (cubeAverage Q energy) := by
    intro N
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
  simpa using cubeBesovNegativeVectorSeminorm_le_of_partialBound Q s g hpartial

theorem coarsePoincare_flux_qone_of_cubeAverageEnergyControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    cubeBesovNegativeVectorSeminorm Q s flux ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on henergy_nonneg
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos hs1
  have hpartial :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N flux ≤
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
            Real.sqrt (cubeAverage Q energy) := by
    intro N
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
  simpa using cubeBesovNegativeVectorSeminorm_le_of_partialBound Q s flux hpartial

/-- Note-facing `q = 1` gradient and flux coarse Poincare bounds under direct
descendant cube-average energy control. -/
theorem coarsePoincare_qone_note_bounds_of_cubeAverageEnergyControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (g flux : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hflux : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum_grad :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsum_flux :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    cubeBesovNegativeVectorSeminorm Q s g ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) ∧
    cubeBesovNegativeVectorSeminorm Q s flux ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q energy) := by
  refine ⟨?_, ?_⟩
  · exact
      coarsePoincare_gradient_qone_of_cubeAverageEnergyControl
        (Q := Q) (a := a) (s := s) hs (g := g) (energy := energy)
        henergy_nonneg henergy_int hgrad hsum_grad
  · exact
      coarsePoincare_flux_qone_of_cubeAverageEnergyControl
        (Q := Q) (a := a) (s := s) hs (flux := flux) (energy := energy)
        henergy_nonneg henergy_int hflux hsum_flux


/-- Note-facing `q = 1` gradient and flux coarse Poincare bounds for one
harmonic field on the parent cube. -/
theorem coarsePoincare_qone_note_bounds_of_aHarmonicFunction
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q)) :
    cubeBesovNegativeVectorSeminorm Q s (fun x => u.toH1.grad x) ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a u x)) ∧
    cubeBesovNegativeVectorSeminorm Q s (fun x => matVecMul (a x) (u.toH1.grad x)) ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a u x)) := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hsum_grad :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) s hs hEll hOrigin
  have hsum_flux :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) s hs hEll hOrigin
  exact
    coarsePoincare_qone_note_bounds_of_cubeAverageEnergyControl
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
