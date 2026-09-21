/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.DepthWeightAlgebra

/-! # Global Base Bounds -/

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSParentHalfCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 ≤ coarsePoincareRHSParentHalfCoeff Q a s n := by
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hshalf2_nonneg : 0 ≤ (s / 2) * (2 : ℝ) := by nlinarith
  unfold coarsePoincareRHSParentHalfCoeff
  exact mul_nonneg
    (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
    (mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (inv_nonneg.mpr
        (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
          (by norm_num) hshalf2_nonneg)))


theorem coarsePoincareRHSGlobalForceBound_nonneg {d : ℕ}
    (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ) :
    0 ≤ coarsePoincareRHSGlobalForceBound Q g s n := by
  unfold coarsePoincareRHSGlobalForceBound
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _)

theorem coarsePoincareRHSSIntrinsicGlobalEnergyBase_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    {s CE : ℝ} (hs : 0 < s) (hCE_nonneg : 0 ≤ CE)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u)) (m : ℕ) :
    0 ≤ coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m := by
  unfold coarsePoincareRHSSIntrinsicGlobalEnergyBase
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (mul_nonneg hCE_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (coarsePoincareRHSParentHalfCoeff_nonneg Q a hs m))
        havg_nonneg))

/-- The depth-scaled global energy base is independent of the starting depth. -/
theorem coarsePoincareRHSSIntrinsicGlobalEnergyBase_succ {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s CE : ℝ) (n : ℕ) :
    coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE (n + 1) =
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE n := by
  let Dsucc : ℝ := coarsePoincareRHSDepthWeight s (n + 1)
  let D : ℝ := coarsePoincareRHSDepthWeight s n
  let Psucc : ℝ := coarsePoincareRHSParentHalfCoeff Q a s (n + 1)
  let P : ℝ := coarsePoincareRHSParentHalfCoeff Q a s n
  let A : ℝ := cubeAverage Q (coefficientEnergyDensity a u)
  have hDP : Dsucc * Psucc = D * P := by
    simpa [Dsucc, D, Psucc, P] using
      coarsePoincareRHSDepthWeight_mul_parentHalfCoeff_succ Q a s n
  calc
    coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE (n + 1)
        = CE * 2 * A * (Dsucc * Psucc) := by
          simp [coarsePoincareRHSSIntrinsicGlobalEnergyBase, Dsucc, Psucc, A]
          ring
    _ = CE * 2 * A * (D * P) := by rw [hDP]
    _ = coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE n := by
          simp [coarsePoincareRHSSIntrinsicGlobalEnergyBase, D, P, A]
          ring

theorem coarsePoincareRHSSIntrinsicGlobalEnergyBase_eq_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s CE : ℝ) (m : ℕ) :
    coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m =
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE 0 := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [coarsePoincareRHSSIntrinsicGlobalEnergyBase_succ Q a u s CE n, ih]

theorem coarsePoincareRHSSIntrinsicGlobalEnergyBase_zero_noteConstants_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u)) :
    coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 0 * (5 * s⁻¹) ≤
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        cubeAverage Q (coefficientEnergyDensity a u) := by
  let K : ℝ := 5 * s⁻¹
  let L : ℝ := (lambdaSqFinite Q (s / 2) 2 a)⁻¹
  let A : ℝ := cubeAverage Q (coefficientEnergyDensity a u)
  let P : ℝ := coarsePoincareRHSParentHalfCoeff Q a s 0
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith [hs]))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact havg_nonneg
  have hP_le : P ≤ K * L := by
    dsimp [P, K, L]
    unfold coarsePoincareRHSParentHalfCoeff
    simpa [lambdaSq, L] using
      mul_le_mul_of_nonneg_right
        (inv_geometricDiscount_two_le_five_inv hs hs_le) hL_nonneg
  have hinner :
      2 * P * A ≤ 2 * (K * L) * A := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hP_le (by norm_num : 0 ≤ (2 : ℝ))) hA_nonneg
  calc
    coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 0 * (5 * s⁻¹)
        = 5 * (2 * P * A) * K := by
          simp [coarsePoincareRHSSIntrinsicGlobalEnergyBase, coarsePoincareRHSDepthWeight,
            P, K, A]
    _ ≤ 5 * (2 * (K * L) * A) * K := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinner (by norm_num : 0 ≤ (5 : ℝ))) hK_nonneg
    _ =
        250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a u) := by
          simp [K, L, A, lambdaSq]
          ring

theorem coarsePoincareRHSSIntrinsicGlobalEnergyBase_noteConstants_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (m : ℕ) :
    coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 m * (5 * s⁻¹) ≤
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        cubeAverage Q (coefficientEnergyDensity a u) := by
  rw [coarsePoincareRHSSIntrinsicGlobalEnergyBase_eq_zero Q a u s 5 m]
  exact
    coarsePoincareRHSSIntrinsicGlobalEnergyBase_zero_noteConstants_le
      Q a u hs hs_le havg_nonneg

theorem coarsePoincareRHSSIntrinsicGlobalForceBase_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) {CF : ℝ} (hCF_nonneg : 0 ≤ CF) (m : ℕ) :
    0 ≤ coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m := by
  unfold coarsePoincareRHSSIntrinsicGlobalForceBase
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (mul_nonneg hCF_nonneg
        (mul_nonneg (sq_nonneg _)
          (coarsePoincareRHSGlobalForceBound_nonneg Q g s m)))

/-- The depth-scaled global force base decays by one `3^{-s}` factor. -/
theorem coarsePoincareRHSSIntrinsicGlobalForceBase_succ {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s CF : ℝ) (n : ℕ) :
    coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF (n + 1) =
      Real.rpow (3 : ℝ) (-s) *
        coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF n := by
  let Dsucc : ℝ := coarsePoincareRHSDepthWeight s (n + 1)
  let D : ℝ := coarsePoincareRHSDepthWeight s n
  let Msucc : ℝ := coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (n + 1)
  let M : ℝ := coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n
  let Fsucc : ℝ := coarsePoincareRHSGlobalForceBound Q g s (n + 1)
  let F : ℝ := coarsePoincareRHSGlobalForceBound Q g s n
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  have hfactor : Dsucc * (Msucc ^ 2 * Fsucc) = r * (D * (M ^ 2 * F)) := by
    simpa [Dsucc, D, Msucc, M, Fsucc, F, r] using
      coarsePoincareRHSIntrinsicForceFactor_succ Q a g s n
  calc
    coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF (n + 1)
        = CF * (Dsucc * (Msucc ^ 2 * Fsucc)) := by
          simp [coarsePoincareRHSSIntrinsicGlobalForceBase, Dsucc, Msucc, Fsucc]
          ring
    _ = CF * (r * (D * (M ^ 2 * F))) := by rw [hfactor]
    _ = r * coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF n := by
          simp [coarsePoincareRHSSIntrinsicGlobalForceBase, D, M, F, r]
          ring

theorem coarsePoincareRHSSIntrinsicGlobalForceBase_le_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s CF : ℝ} (hs_nonneg : 0 ≤ s) (hCF_nonneg : 0 ≤ CF) (m : ℕ) :
    coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m ≤
      coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF 0 := by
  have hr_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-s) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_le_one : Real.rpow (3 : ℝ) (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  induction m with
  | zero => rfl
  | succ n ih =>
      have hbase_nonneg :
          0 ≤ coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF n :=
        coarsePoincareRHSSIntrinsicGlobalForceBase_nonneg
          Q a g s hCF_nonneg n
      calc
        coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF (n + 1)
            = Real.rpow (3 : ℝ) (-s) *
                coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF n := by
              rw [coarsePoincareRHSSIntrinsicGlobalForceBase_succ]
        _ ≤ 1 * coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF n :=
              mul_le_mul_of_nonneg_right hr_le_one hbase_nonneg
        _ = coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF n := by ring
        _ ≤ coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF 0 := ih

theorem coarsePoincareRHSSIntrinsicGlobalForceBase_zero_noteConstants_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) :
    coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) 0 * (5 * s⁻¹) ≤
      15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let K : ℝ := 5 * s⁻¹
  let L : ℝ := (lambdaSqFinite Q (s / 2) 2 a)⁻¹
  let P : ℝ := coarsePoincareRHSParentHalfCoeff Q a s 0
  let M : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith [hs]))
  have hKL_nonneg : 0 ≤ K * L := mul_nonneg hK_nonneg hL_nonneg
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact coarsePoincareRHSParentHalfCoeff_nonneg Q a hs 0
  have hP_le : P ≤ K * L := by
    dsimp [P, K, L]
    unfold coarsePoincareRHSParentHalfCoeff
    simpa [lambdaSq, L] using
      mul_le_mul_of_nonneg_right
        (inv_geometricDiscount_two_le_five_inv hs hs_le) hL_nonneg
  have hP_sq : P ^ 2 ≤ (K * L) ^ 2 := by
    have habs : |P| ≤ |K * L| := by
      simpa [abs_of_nonneg hP_nonneg, abs_of_nonneg hKL_nonneg] using hP_le
    exact sq_le_sq.mpr habs
  have hmult_nonneg : 0 ≤ (120 * s⁻¹) * M ^ 2 * B ^ 2 * K := by
    dsimp [K, M, B]
    positivity
  calc
    coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) 0 * (5 * s⁻¹)
        = P ^ 2 * ((120 * s⁻¹) * M ^ 2 * B ^ 2 * K) := by
          simp [coarsePoincareRHSSIntrinsicGlobalForceBase, coarsePoincareRHSDepthWeight,
            coarsePoincareRHSIntrinsicParentHalfForceMultiplier,
            coarsePoincareRHSGlobalForceBound, P, M, B, K]
          ring
    _ ≤ (K * L) ^ 2 * ((120 * s⁻¹) * M ^ 2 * B ^ 2 * K) := by
          exact mul_le_mul_of_nonneg_right hP_sq hmult_nonneg
    _ =
        15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
          simp [K, L, M, B, lambdaSq]
          ring

theorem coarsePoincareRHSSIntrinsicGlobalForceBase_noteConstants_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (m : ℕ) :
    coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) m * (5 * s⁻¹) ≤
      15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hK_nonneg : 0 ≤ 5 * s⁻¹ := by positivity
  have hbase_le :
      coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) m ≤
        coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) 0 :=
    coarsePoincareRHSSIntrinsicGlobalForceBase_le_zero Q a g
      hs.le (by positivity) m
  exact
    (mul_le_mul_of_nonneg_right hbase_le hK_nonneg).trans
      (coarsePoincareRHSSIntrinsicGlobalForceBase_zero_noteConstants_le
        Q a g hs hs_le)

theorem coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum_eq_base_mul_geomSum
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s θ CE : ℝ) (m N : ℕ) :
    coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N =
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m *
        ∑ k ∈ Finset.range N, (coarsePoincareRHSFiniteSumRatio s θ) ^ k := by
  unfold coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum
    coarsePoincareRHSSIntrinsicGlobalEnergyBase
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hcoeff :=
    coarsePoincareRHSWeightedDepthParentHalfCoeff_eq_base_mul_ratio_pow
      Q a s θ m k
  calc
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
        (coarsePoincareRHSDepthWeight s (m + k) *
          (CE *
            (2 * coarsePoincareRHSParentHalfCoeff Q a s (m + k) *
              cubeAverage Q (coefficientEnergyDensity a u))))
        =
      (CE * 2 * cubeAverage Q (coefficientEnergyDensity a u)) *
        ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
          (coarsePoincareRHSDepthWeight s (m + k) *
            coarsePoincareRHSParentHalfCoeff Q a s (m + k))) := by
        ring
    _ =
      (CE * 2 * cubeAverage Q (coefficientEnergyDensity a u)) *
        ((coarsePoincareRHSDepthWeight s m *
            coarsePoincareRHSParentHalfCoeff Q a s m) *
          (coarsePoincareRHSFiniteSumRatio s θ) ^ k) := by
        rw [hcoeff]
    _ =
      coarsePoincareRHSDepthWeight s m *
          (CE *
            (2 * coarsePoincareRHSParentHalfCoeff Q a s m *
              cubeAverage Q (coefficientEnergyDensity a u))) *
        (coarsePoincareRHSFiniteSumRatio s θ) ^ k := by
        ring

theorem coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum_le_base_mul_inv_one_sub
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s θ CE : ℝ) (m N : ℕ)
    (hr_nonneg : 0 ≤ coarsePoincareRHSFiniteSumRatio s θ)
    (hr_lt_one : coarsePoincareRHSFiniteSumRatio s θ < 1)
    (hbase_nonneg : 0 ≤ coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m) :
    coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N ≤
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m *
        (1 - coarsePoincareRHSFiniteSumRatio s θ)⁻¹ := by
  rw [coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum_eq_base_mul_geomSum]
  exact mul_le_mul_of_nonneg_left
    (geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one) hbase_nonneg

theorem coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum_le_base_mul_inv_one_sub_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    {s θ CE : ℝ} (m N : ℕ) (hs : 0 < s) (hCE_nonneg : 0 ≤ CE)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (hr_nonneg : 0 ≤ coarsePoincareRHSFiniteSumRatio s θ)
    (hr_lt_one : coarsePoincareRHSFiniteSumRatio s θ < 1) :
    coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum Q a u s θ CE m N ≤
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s CE m *
        (1 - coarsePoincareRHSFiniteSumRatio s θ)⁻¹ := by
  exact
    coarsePoincareRHSSIntrinsicWeightedGlobalEnergyErrorSum_le_base_mul_inv_one_sub
      Q a u s θ CE m N hr_nonneg hr_lt_one
      (coarsePoincareRHSSIntrinsicGlobalEnergyBase_nonneg
        Q a u hs hCE_nonneg havg_nonneg m)

theorem coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum_eq_base_mul_geomSum
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s θ CF : ℝ) (m N : ℕ) :
    coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N =
      coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m *
        ∑ k ∈ Finset.range N, (coarsePoincareRHSForceFiniteSumRatio s θ) ^ k := by
  unfold coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum
    coarsePoincareRHSSIntrinsicGlobalForceBase
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hfactor :=
    coarsePoincareRHSIntrinsicWeightedForceFactor_eq_base_mul_ratio_pow
      Q a g s θ m k
  calc
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
        (coarsePoincareRHSDepthWeight s (m + k) *
          (CF *
            ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
              coarsePoincareRHSGlobalForceBound Q g s (m + k))))
        =
      CF *
        ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
          (coarsePoincareRHSDepthWeight s (m + k) *
            ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
              coarsePoincareRHSGlobalForceBound Q g s (m + k)))) := by
        ring
    _ =
      CF *
        ((coarsePoincareRHSDepthWeight s m *
          ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s m) ^ 2 *
            coarsePoincareRHSGlobalForceBound Q g s m)) *
          (coarsePoincareRHSForceFiniteSumRatio s θ) ^ k) := by
        rw [hfactor]
    _ =
      coarsePoincareRHSDepthWeight s m *
          (CF *
            ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s m) ^ 2 *
              coarsePoincareRHSGlobalForceBound Q g s m)) *
        (coarsePoincareRHSForceFiniteSumRatio s θ) ^ k := by
        ring

theorem coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum_le_base_mul_inv_one_sub
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s θ CF : ℝ) (m N : ℕ)
    (hr_nonneg : 0 ≤ coarsePoincareRHSForceFiniteSumRatio s θ)
    (hr_lt_one : coarsePoincareRHSForceFiniteSumRatio s θ < 1)
    (hbase_nonneg : 0 ≤ coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m) :
    coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N ≤
      coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m *
        (1 - coarsePoincareRHSForceFiniteSumRatio s θ)⁻¹ := by
  rw [coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum_eq_base_mul_geomSum]
  exact mul_le_mul_of_nonneg_left
    (geom_sum_range_le_of_lt_one hr_nonneg hr_lt_one) hbase_nonneg

theorem coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum_le_base_mul_inv_one_sub_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s θ CF : ℝ} (m N : ℕ) (hCF_nonneg : 0 ≤ CF)
    (hr_nonneg : 0 ≤ coarsePoincareRHSForceFiniteSumRatio s θ)
    (hr_lt_one : coarsePoincareRHSForceFiniteSumRatio s θ < 1) :
    coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum Q a g s θ CF m N ≤
      coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s CF m *
        (1 - coarsePoincareRHSForceFiniteSumRatio s θ)⁻¹ := by
  exact
    coarsePoincareRHSSIntrinsicWeightedGlobalForceErrorSum_le_base_mul_inv_one_sub
      Q a g s θ CF m N hr_nonneg hr_lt_one
      (coarsePoincareRHSSIntrinsicGlobalForceBase_nonneg Q a g s hCF_nonneg m)


end

end Homogenization
