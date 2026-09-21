/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge

/-! # Sharp Loss -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Sharp-loss positive-test route

This file keeps the honest low-exponent sharp-boundary loss visible in the
scalar duality assembly.  The bridge is only used for exponents below `1/2`,
and the public RHS carries the corresponding factor
`1 + sqrt (sharpBoundaryKernelLoss d t)`.
-/

/-- Genuine-dual solution-comparison estimate with the sharp boundary loss
shown explicitly. -/
def ScalarSolutionComparisonGenuineDualityEstimateSharpLoss
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) (sigma0 : ℝ) (w F : Vec d → Vec d)
      {t : ℝ} (j : ℕ),
      0 < sigma0 →
      0 < t →
      t < 1 / 2 →
      MemVectorL2 (cubeSet Q) F →
      IsPotentialZeroTraceOn (cubeSet Q) w →
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
            (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        C * (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) * t⁻¹ *
          localizedFluxDefectNegativeBesovAverageTwo Q t F j

/-- One-parameter concrete/circ scalar duality estimate with the flux defect
measured at `s / 2` and the sharp-boundary bridge loss displayed. -/
def ScalarSolutionComparisonDualityEstimateHalfExponentSharpLoss
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) (sigma0 : ℝ) (w F : Vec d → Vec d)
      {s : ℝ} (j : ℕ),
      0 < sigma0 →
      0 < s →
      s < 1 →
      MemVectorL2 (cubeSet Q) F →
      IsPotentialZeroTraceOn (cubeSet Q) w →
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) →
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        C * (1 + Real.sqrt (sharpBoundaryKernelLoss d (s / 2))) *
          (s⁻¹) ^ (3 : ℕ) *
            localizedFluxDefectNegativeBesovAverageTwo Q (s / 2) F j

/-- Two-exponent concrete/circ scalar duality estimate with the manuscript
loss `s^{-1} t^{-2} (1/2 - t)^{-1}`. -/
def ScalarSolutionComparisonDualityEstimateExponentLoss
    (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (Q : TriadicCube d) (sigma0 : ℝ) (w F : Vec d → Vec d)
      {s t : ℝ} (j : ℕ),
      0 < sigma0 →
      0 < s →
      0 < t →
      t < s / 2 →
      s < 1 →
      MemVectorL2 (cubeSet Q) F →
      IsPotentialZeroTraceOn (cubeSet Q) w →
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) →
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        C * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ *
          localizedFluxDefectNegativeBesovAverageTwo Q t F j

/-- Dimension-only constant bounding the sharp-boundary loss by the displayed
`(1/2 - t)^{-1}` singularity. -/
noncomputable def sharpBoundaryKernelNoteConstant (d : ℕ) : ℝ :=
  1 + Real.sqrt (8 * (3 ^ d : ℝ) +
    100 * (sharpBoundaryKernelConstant d) ^ (2 : ℕ))

theorem sharpBoundaryKernelNoteConstant_nonneg (d : ℕ) :
    0 ≤ sharpBoundaryKernelNoteConstant d := by
  unfold sharpBoundaryKernelNoteConstant
  positivity

theorem one_add_sqrt_sharpBoundaryKernelLoss_le_noteConstant
    {d : ℕ} [NeZero d] {t : ℝ}
    (ht : 0 < t) (ht_lt_half : t < 1 / 2) :
    1 + Real.sqrt (sharpBoundaryKernelLoss d t) ≤
      sharpBoundaryKernelNoteConstant d * ((1 / 2 : ℝ) - t)⁻¹ := by
  let r : ℝ := (1 / 2 : ℝ) - t
  let A : ℝ := 8 * (3 ^ d : ℝ) +
    100 * (sharpBoundaryKernelConstant d) ^ (2 : ℕ)
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  have hr_le_one : r ≤ 1 := by
    dsimp [r]
    linarith
  have hr_inv_nonneg : 0 ≤ r⁻¹ := inv_nonneg.mpr hr_pos.le
  have hr_inv_ge_one : 1 ≤ r⁻¹ := (one_le_inv₀ hr_pos).2 hr_le_one
  have hr_inv_sq_ge_one : 1 ≤ (r⁻¹) ^ (2 : ℕ) := by
    simpa using
      (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hr_inv_ge_one 2)
  have hbase_eq : sharpBoundaryKernelBase d t = Real.rpow (3 : ℝ) (-r) := by
    rw [sharpBoundaryKernelBase_eq]
    congr 1
    dsimp [r]
    ring
  have hinv_le :
      (1 - sharpBoundaryKernelBase d t)⁻¹ ≤ 5 * r⁻¹ := by
    rw [hbase_eq]
    exact inv_one_sub_rpow_three_neg_le_five_inv hr_pos hr_le_one
  have hbase_lt_one : sharpBoundaryKernelBase d t < 1 :=
    sharpBoundaryKernelBase_lt_one (d := d) (t := t) ht_lt_half
  have hinv_nonneg :
      0 ≤ (1 - sharpBoundaryKernelBase d t)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hbase_lt_one.le)
  have hinv_sq_le :
      ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ (2 : ℕ) ≤
        (5 * r⁻¹) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hinv_nonneg hinv_le 2
  have hK_nonneg : 0 ≤ sharpBoundaryKernelConstant d :=
    sharpBoundaryKernelConstant_nonneg d
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hloss_le :
      sharpBoundaryKernelLoss d t ≤ A * (r⁻¹) ^ (2 : ℕ) := by
    unfold sharpBoundaryKernelLoss
    dsimp [A]
    calc
      8 * (3 ^ d : ℝ) +
          (4 * (sharpBoundaryKernelConstant d) ^ 2) *
            ((1 - sharpBoundaryKernelBase d t)⁻¹) ^ 2
          ≤
        8 * (3 ^ d : ℝ) * (r⁻¹) ^ (2 : ℕ) +
          (4 * (sharpBoundaryKernelConstant d) ^ 2) *
            (5 * r⁻¹) ^ (2 : ℕ) := by
          have hfirst :
              8 * (3 ^ d : ℝ) ≤
                8 * (3 ^ d : ℝ) * (r⁻¹) ^ (2 : ℕ) := by
            have hcoeff_nonneg : 0 ≤ 8 * (3 ^ d : ℝ) :=
              mul_nonneg (by norm_num : 0 ≤ (8 : ℝ))
                (pow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) d)
            calc
              8 * (3 ^ d : ℝ) = 8 * (3 ^ d : ℝ) * 1 := by ring
              _ ≤ 8 * (3 ^ d : ℝ) * (r⁻¹) ^ (2 : ℕ) :=
                mul_le_mul_of_nonneg_left hr_inv_sq_ge_one hcoeff_nonneg
          exact add_le_add hfirst
            (mul_le_mul_of_nonneg_left hinv_sq_le
              (mul_nonneg (by norm_num) (sq_nonneg (sharpBoundaryKernelConstant d))))
      _ = (8 * (3 ^ d : ℝ) +
            100 * (sharpBoundaryKernelConstant d) ^ (2 : ℕ)) *
          (r⁻¹) ^ (2 : ℕ) := by ring
  have hsqrt_le :
      Real.sqrt (sharpBoundaryKernelLoss d t) ≤
        Real.sqrt A * r⁻¹ := by
    calc
      Real.sqrt (sharpBoundaryKernelLoss d t) ≤
          Real.sqrt (A * (r⁻¹) ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hloss_le
      _ = Real.sqrt A * r⁻¹ := by
        rw [Real.sqrt_mul hA_nonneg, Real.sqrt_sq hr_inv_nonneg]
  calc
    1 + Real.sqrt (sharpBoundaryKernelLoss d t)
        ≤ r⁻¹ + Real.sqrt A * r⁻¹ := by
          exact add_le_add hr_inv_ge_one hsqrt_le
    _ = sharpBoundaryKernelNoteConstant d * r⁻¹ := by
          unfold sharpBoundaryKernelNoteConstant
          dsimp [A]
          ring
    _ = sharpBoundaryKernelNoteConstant d * ((1 / 2 : ℝ) - t)⁻¹ := by
          rfl

/-- The Ch1 exponent-loss gap has the note-facing two-exponent singularity
when the input exponent is below half the output exponent. -/
theorem besovExponentLossGap_le_note {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hts : t < s / 2) (hs_lt_one : s < 1) :
    besovExponentLossGap s t ≤ 110 * s⁻¹ * t⁻¹ := by
  let A : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let B : ℝ := (1 - Real.rpow (3 : ℝ) (-t))⁻¹
  let D : ℝ := (1 - Real.rpow (3 : ℝ) (-(s - t)))⁻¹
  have hs_le_one : s ≤ 1 := hs_lt_one.le
  have ht_le_one : t ≤ 1 := by linarith
  have hst_pos : 0 < s - t := by linarith
  have hst_le_one : s - t ≤ 1 := by linarith
  have hA_le : A ≤ 5 * s⁻¹ := by
    dsimp [A]
    exact inv_one_sub_rpow_three_neg_le_five_inv hs hs_le_one
  have hB_le : B ≤ 5 * t⁻¹ := by
    dsimp [B]
    exact inv_one_sub_rpow_three_neg_le_five_inv ht ht_le_one
  have hD_le_raw : D ≤ 5 * (s - t)⁻¹ := by
    dsimp [D]
    exact inv_one_sub_rpow_three_neg_le_five_inv hst_pos hst_le_one
  have hhalf_le_gap : s / 2 ≤ s - t := by linarith
  have hs_half_pos : 0 < s / 2 := by positivity
  have hgap_inv_le : (s - t)⁻¹ ≤ (s / 2)⁻¹ :=
    (inv_le_inv₀ hst_pos hs_half_pos).2 hhalf_le_gap
  have hhalf_inv : (s / 2)⁻¹ = 2 * s⁻¹ := by
    field_simp [hs.ne']
  have hD_le : D ≤ 10 * s⁻¹ := by
    calc
      D ≤ 5 * (s - t)⁻¹ := hD_le_raw
      _ ≤ 5 * (s / 2)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hgap_inv_le (by norm_num)
      _ = 10 * s⁻¹ := by rw [hhalf_inv]; ring
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hr_lt : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt.le)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hr_lt : Real.rpow (3 : ℝ) (-t) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt.le)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    have hr_lt : Real.rpow (3 : ℝ) (-(s - t)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt.le)
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have ht_inv_nonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have ht_inv_ge_one : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht_le_one
  unfold besovExponentLossGap
  change A + (2 * B) * D ≤ 110 * s⁻¹ * t⁻¹
  have hA_note : A ≤ 10 * s⁻¹ * t⁻¹ := by
    have hfive_s_nonneg : 0 ≤ 5 * s⁻¹ :=
      mul_nonneg (by norm_num : 0 ≤ (5 : ℝ)) hs_inv_nonneg
    have hfive_s_le_ten_s : 5 * s⁻¹ ≤ 10 * s⁻¹ :=
      mul_le_mul_of_nonneg_right (by norm_num : (5 : ℝ) ≤ 10) hs_inv_nonneg
    calc
      A ≤ 5 * s⁻¹ := hA_le
      _ = 5 * s⁻¹ * 1 := by ring
      _ ≤ 5 * s⁻¹ * t⁻¹ :=
        mul_le_mul_of_nonneg_left ht_inv_ge_one hfive_s_nonneg
      _ ≤ 10 * s⁻¹ * t⁻¹ :=
        mul_le_mul_of_nonneg_right hfive_s_le_ten_s ht_inv_nonneg
  have hBD_note : (2 * B) * D ≤ 100 * s⁻¹ * t⁻¹ := by
    have htwoB_le : 2 * B ≤ 2 * (5 * t⁻¹) :=
      mul_le_mul_of_nonneg_left hB_le (by norm_num : 0 ≤ (2 : ℝ))
    have hB_bound_nonneg : 0 ≤ 2 * (5 * t⁻¹) :=
      mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (mul_nonneg (by norm_num : 0 ≤ (5 : ℝ)) ht_inv_nonneg)
    calc
      (2 * B) * D ≤ (2 * (5 * t⁻¹)) * (10 * s⁻¹) :=
        mul_le_mul htwoB_le hD_le hD_nonneg hB_bound_nonneg
      _ = 100 * s⁻¹ * t⁻¹ := by ring
  calc
    A + (2 * B) * D ≤ 10 * s⁻¹ * t⁻¹ + 100 * s⁻¹ * t⁻¹ :=
      add_le_add hA_note hBD_note
    _ = 110 * s⁻¹ * t⁻¹ := by ring

/-- Coordinate-test Dirichlet solution bound using the low-exponent
sharp-loss bridge. -/
theorem exists_coordinateDirichletSolution_overlappingPositiveNorm_le_sharpLoss
    {d : ℕ} [NeZero d] {Cdir Cbridge : ℝ}
    (hdir : DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform d Cdir)
    (hbridge : UnitFullDualCoordinateOverlappingBridgeSharpLoss d Cbridge)
    (Q : TriadicCube d) {s : ℝ} (i : Fin d) (g : Vec d → ℝ)
    (hs : 0 < s) (hs_lt_half : s < 1 / 2)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    ∃ w : H10Function (openCubeSet Q),
      CubeDirichletDivergenceProblem Q w (coordinateVectorField i g) ∧
        CubeVectorOverlappingBesovHRegularity Q s
            (fun x => w.toH1Function.grad x) ∧
        cubeBesovOverlappingPositiveVectorNormTwo Q s
            (fun x => w.toH1Function.grad x) ≤
          Cdir *
            (Cbridge * (1 + Real.sqrt (sharpBoundaryKernelLoss d s)) *
              cubeBesovScaleWeight (-s) Q) := by
  have hs_lt_one : s < 1 := by nlinarith
  have hh :
      MeasureTheory.MemLp (coordinateVectorField i g) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two hg
  rcases exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure
      (Q := Q) hh with
    ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  rcases hbridge.2 Q i g hs hs_lt_half hg with
    ⟨hreg, hbridgeBound⟩
  have hdirBound :
      CubeVectorOverlappingBesovHRegularity Q s
          (fun x => w.toH1Function.grad x) ∧
        cubeBesovOverlappingPositiveVectorNormTwo Q s
            (fun x => w.toH1Function.grad x) ≤
          Cdir *
            cubeBesovOverlappingPositiveVectorNormTwo Q s
              (coordinateVectorField i g) :=
    hdir.2 hs hs_lt_one Q (coordinateVectorField i g) w hreg hw
  exact ⟨hdirBound.1, hdirBound.2.trans
    (mul_le_mul_of_nonneg_left hbridgeBound hdir.1)⟩

/-- Componentwise scalar full-dual pairing bounds with the sharp loss control
the vector genuine-dual solution-comparison estimate with the same displayed
loss. -/
theorem scalarSolutionComparisonGenuineDualityEstimateSharpLoss_of_component_fullTest_pairing_bounds
    {d : ℕ} [NeZero d] {Cpair : ℝ}
    (hCpair : 0 ≤ Cpair)
    (hSigma :
      ∀ (Q : TriadicCube d) (sigma0 : ℝ) (w F : Vec d → Vec d)
        {t : ℝ} (j : ℕ),
        0 < sigma0 →
        0 < t →
        t < 1 / 2 →
        MemVectorL2 (cubeSet Q) F →
        IsPotentialZeroTraceOn (cubeSet Q) w →
        IsSolenoidalOn (cubeSet Q)
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) →
        ∀ (i : Fin d) (g : Vec d → ℝ),
          CubeBesovDualFullTest Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
            |cubeBesovPairing Q
              (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) i) g| ≤
              Cpair * (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) *
                t⁻¹ * cubeBesovScaleWeight (-t) Q *
                  localizedFluxDefectNegativeBesovAverageTwo Q t F j)
    (hFlux :
      ∀ (Q : TriadicCube d) (sigma0 : ℝ) (w F : Vec d → Vec d)
        {t : ℝ} (j : ℕ),
        0 < sigma0 →
        0 < t →
        t < 1 / 2 →
        MemVectorL2 (cubeSet Q) F →
        IsPotentialZeroTraceOn (cubeSet Q) w →
        IsSolenoidalOn (cubeSet Q)
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) →
        ∀ (i : Fin d) (g : Vec d → ℝ),
          CubeBesovDualFullTest Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
            |cubeBesovPairing Q
              (fun x => (matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) i)
              g| ≤
              Cpair * (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) *
                t⁻¹ * cubeBesovScaleWeight (-t) Q *
                  localizedFluxDefectNegativeBesovAverageTwo Q t F j) :
    ScalarSolutionComparisonGenuineDualityEstimateSharpLoss d
      (2 * (Fintype.card (Fin d) : ℝ) * Cpair) := by
  refine ⟨?_, ?_⟩
  · have hcard : 0 ≤ (Fintype.card (Fin d) : ℝ) := by positivity
    nlinarith
  intro Q sigma0 w F t j hsigma0 ht ht_lt_half hF hw hsol
  let K : ℝ := 1 + Real.sqrt (sharpBoundaryKernelLoss d t)
  let L : ℝ := localizedFluxDefectNegativeBesovAverageTwo Q t F j
  let B : ℝ := Cpair * K * t⁻¹ * cubeBesovScaleWeight (-t) Q * L
  have hSigmaNorm :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) ≤
        cubeBesovScaleWeight t Q * ((Fintype.card (Fin d) : ℝ) * B) :=
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul_of_forall_component_fullTest_pairing_le
      Q t (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x))
      (B := B)
      (fun i g hg => by
        dsimp [B, K, L]
        exact hSigma Q sigma0 w F j hsigma0 ht ht_lt_half hF hw hsol i g hg)
  have hFluxNorm :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        cubeBesovScaleWeight t Q * ((Fintype.card (Fin d) : ℝ) * B) :=
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul_of_forall_component_fullTest_pairing_le
      Q t (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)
      (B := B)
      (fun i g hg => by
        dsimp [B, K, L]
        exact hFlux Q sigma0 w F j hsigma0 ht ht_lt_half hF hw hsol i g hg)
  have hscale :
      cubeBesovScaleWeight t Q * ((Fintype.card (Fin d) : ℝ) * B) =
        ((Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L := by
    dsimp [B, K, L]
    calc
      cubeBesovScaleWeight t Q *
          ((Fintype.card (Fin d) : ℝ) *
            (Cpair * (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) *
              t⁻¹ * cubeBesovScaleWeight (-t) Q *
                localizedFluxDefectNegativeBesovAverageTwo Q t F j))
          =
            (cubeBesovScaleWeight t Q * cubeBesovScaleWeight (-t) Q) *
              (((Fintype.card (Fin d) : ℝ) * Cpair) *
                (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) * t⁻¹ *
                  localizedFluxDefectNegativeBesovAverageTwo Q t F j) := by
            ring
      _ =
            1 * (((Fintype.card (Fin d) : ℝ) * Cpair) *
              (1 + Real.sqrt (sharpBoundaryKernelLoss d t)) * t⁻¹ *
                localizedFluxDefectNegativeBesovAverageTwo Q t F j) := by
            rw [cubeBesovScaleWeight_mul_neg_self]
      _ =
            ((Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L := by
            dsimp [K, L]
            ring
  have hSigmaNorm' :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) ≤
        ((Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L := by
    exact hSigmaNorm.trans (le_of_eq hscale)
  have hFluxNorm' :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) ≤
        ((Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L := by
    exact hFluxNorm.trans (le_of_eq hscale)
  calc
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)
        ≤
          ((Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L +
            ((Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L :=
      add_le_add hSigmaNorm' hFluxNorm'
    _ =
        (2 * (Fintype.card (Fin d) : ℝ) * Cpair) * K * t⁻¹ * L := by
      ring

/--
Close the genuine-dual scalar solution-comparison estimate from the restored
LaTeX argument, but using the honest low-exponent coordinate bridge with the
sharp-boundary loss displayed.
-/
theorem scalarSolutionComparisonGenuineDualityEstimateSharpLoss_of_dirichletBesov_of_coordinateBridgeSharpLoss_of_localizedPairing
    {d : ℕ} [NeZero d] {Cdir Cbridge Cpairing : ℝ}
    (hdir : DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform d Cdir)
    (hbridge : UnitFullDualCoordinateOverlappingBridgeSharpLoss d Cbridge)
    (hpair : LocalizedFluxDefectPositivePairingEstimate d Cpairing) :
    ScalarSolutionComparisonGenuineDualityEstimateSharpLoss d
      (2 * (Fintype.card (Fin d) : ℝ) *
        (Cpairing * (Cdir + 1) * Cbridge)) := by
  let Ccomponent : ℝ := Cpairing * (Cdir + 1) * Cbridge
  have hCcomponent : 0 ≤ Ccomponent := by
    have hCdir1 : 0 ≤ Cdir + 1 := by linarith [hdir.1]
    exact mul_nonneg (mul_nonneg hpair.1 hCdir1) hbridge.1
  refine
    scalarSolutionComparisonGenuineDualityEstimateSharpLoss_of_component_fullTest_pairing_bounds
      (d := d) (Cpair := Ccomponent) hCcomponent ?_ ?_
  · intro Q sigma0 w F t j _hsigma0 ht ht_lt_half hF hw hsol i g hg
    let K : ℝ := 1 + Real.sqrt (sharpBoundaryKernelLoss d t)
    let W : ℝ := cubeBesovScaleWeight (-t) Q
    let L : ℝ := localizedFluxDefectNegativeBesovAverageTwo Q t F j
    have ht_lt_one : t < 1 := by linarith
    rcases
        exists_coordinateDirichletSolution_overlappingPositiveNorm_le_sharpLoss
          hdir hbridge Q i g ht ht_lt_half hg with
      ⟨v, hv, hvReg, hvNorm⟩
    have hpairing_eq :
        cubeBesovPairing Q
            (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) i) g =
          cubeAverage Q (fun x => vecDot (F x) (v.toH1Function.grad x)) :=
      cubeBesovPairing_solutionComparison_component_eq_cubeAverage_fluxDefect_dualGradient
        (Q := Q) (sigma0 := sigma0) (w := w) (F := F) (v := v)
        i g hF hv hw hsol
    have hW_nonneg : 0 ≤ W := cubeBesovScaleWeight_nonneg (-t) Q
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hBv_nonneg : 0 ≤ Cdir * (Cbridge * K * W) := by
      exact mul_nonneg hdir.1
        (mul_nonneg (mul_nonneg hbridge.1 hK_nonneg) hW_nonneg)
    have hlocal :
        |cubeAverage Q (fun x => vecDot (F x) (v.toH1Function.grad x))| ≤
          Cpairing * t⁻¹ * L * (Cdir * (Cbridge * K * W)) :=
      hpair.bound Q j F (fun x => v.toH1Function.grad x)
        (Cdir * (Cbridge * K * W)) ht ht_lt_one hF hvReg hBv_nonneg hvNorm
    have htarget :
        Cpairing * t⁻¹ * L * (Cdir * (Cbridge * K * W)) ≤
          Ccomponent * K * t⁻¹ * W * L := by
      have htinv_nonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
      have hL_nonneg : 0 ≤ L :=
        localizedFluxDefectNegativeBesovAverageTwo_nonneg Q t F j
      have hCdir1 : Cdir ≤ Cdir + 1 := by linarith
      have hcoeff :
          Cpairing * Cdir * Cbridge ≤ Cpairing * (Cdir + 1) * Cbridge := by
        calc
          Cpairing * Cdir * Cbridge =
              (Cpairing * Cdir) * Cbridge := by ring
          _ ≤ (Cpairing * (Cdir + 1)) * Cbridge :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hCdir1 hpair.1) hbridge.1
          _ = Cpairing * (Cdir + 1) * Cbridge := by ring
      have htail_nonneg : 0 ≤ K * t⁻¹ * W * L :=
        mul_nonneg (mul_nonneg (mul_nonneg hK_nonneg htinv_nonneg) hW_nonneg)
          hL_nonneg
      calc
        Cpairing * t⁻¹ * L * (Cdir * (Cbridge * K * W))
            = (Cpairing * Cdir * Cbridge) * (K * t⁻¹ * W * L) := by
              ring
        _ ≤ (Cpairing * (Cdir + 1) * Cbridge) *
              (K * t⁻¹ * W * L) :=
              mul_le_mul_of_nonneg_right hcoeff htail_nonneg
        _ = Ccomponent * K * t⁻¹ * W * L := by
              dsimp [Ccomponent]
              ring
    rw [hpairing_eq]
    exact hlocal.trans htarget
  · intro Q sigma0 w F t j _hsigma0 ht ht_lt_half hF hw hsol i g hg
    let K : ℝ := 1 + Real.sqrt (sharpBoundaryKernelLoss d t)
    let W : ℝ := cubeBesovScaleWeight (-t) Q
    let L : ℝ := localizedFluxDefectNegativeBesovAverageTwo Q t F j
    have ht_lt_one : t < 1 := by nlinarith
    rcases
        exists_coordinateDirichletSolution_overlappingPositiveNorm_le_sharpLoss
          hdir hbridge Q i g ht ht_lt_half hg with
      ⟨v, hv, hvReg, hvNorm⟩
    have hpairing_eq :
        cubeBesovPairing Q
            (fun x => (matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) i) g =
          cubeAverage Q
            (fun x => vecDot (F x)
              (v.toH1Function.grad x + coordinateVectorField i g x)) :=
      cubeBesovPairing_fluxComparison_component_eq_cubeAverage_fluxDefect_dualGradient_add_coordinate
        (Q := Q) (sigma0 := sigma0) (w := w) (F := F) (v := v)
        i hg hF hv hw hsol
    have hFOpen : MemVectorL2 (openCubeSet Q) F := by
      simpa [MemVectorL2, volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
        using hF
    have hcoordLp :
        MeasureTheory.MemLp (coordinateVectorField i g) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) :=
      coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two hg
    have hcoordOpen :
        MemVectorL2 (openCubeSet Q) (coordinateVectorField i g) :=
      memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hcoordLp
    have hsplit :
        |cubeAverage Q
            (fun x => vecDot (F x)
              (v.toH1Function.grad x + coordinateVectorField i g x))| ≤
          |cubeAverage Q (fun x => vecDot (F x) (v.toH1Function.grad x))| +
            |cubeAverage Q (fun x => vecDot (F x) (coordinateVectorField i g x))| :=
      abs_cubeAverage_vecDot_add_right_le
        Q F (fun x => v.toH1Function.grad x) (coordinateVectorField i g)
        hFOpen v.toH1Function.grad_memVectorL2 hcoordOpen
    have hW_nonneg : 0 ≤ W := cubeBesovScaleWeight_nonneg (-t) Q
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hBv_nonneg : 0 ≤ Cdir * (Cbridge * K * W) := by
      exact mul_nonneg hdir.1
        (mul_nonneg (mul_nonneg hbridge.1 hK_nonneg) hW_nonneg)
    have hBg_nonneg : 0 ≤ Cbridge * K * W := by
      exact mul_nonneg (mul_nonneg hbridge.1 hK_nonneg) hW_nonneg
    have hlocal_v :
        |cubeAverage Q (fun x => vecDot (F x) (v.toH1Function.grad x))| ≤
          Cpairing * t⁻¹ * L * (Cdir * (Cbridge * K * W)) :=
      hpair.bound Q j F (fun x => v.toH1Function.grad x)
        (Cdir * (Cbridge * K * W)) ht ht_lt_one hF hvReg hBv_nonneg hvNorm
    rcases hbridge.2 Q i g ht ht_lt_half hg with
      ⟨hcoordReg, hcoordNorm⟩
    have hlocal_g :
        |cubeAverage Q (fun x => vecDot (F x) (coordinateVectorField i g x))| ≤
          Cpairing * t⁻¹ * L * (Cbridge * K * W) :=
      hpair.bound Q j F (coordinateVectorField i g)
        (Cbridge * K * W) ht ht_lt_one hF hcoordReg hBg_nonneg hcoordNorm
    have hsum :
        |cubeAverage Q
            (fun x => vecDot (F x)
              (v.toH1Function.grad x + coordinateVectorField i g x))| ≤
          Cpairing * t⁻¹ * L * (Cdir * (Cbridge * K * W)) +
            Cpairing * t⁻¹ * L * (Cbridge * K * W) :=
      hsplit.trans (add_le_add hlocal_v hlocal_g)
    have htarget :
        Cpairing * t⁻¹ * L * (Cdir * (Cbridge * K * W)) +
            Cpairing * t⁻¹ * L * (Cbridge * K * W) ≤
          Ccomponent * K * t⁻¹ * W * L := by
      apply le_of_eq
      dsimp [Ccomponent, K, W, L]
      ring
    rw [hpairing_eq]
    exact hsum.trans htarget

/-- Specialize the sharp-loss genuine-dual estimate to `t = s / 2` and compose
with the proved Ch1 dual-to-circ exponent-loss embedding. -/
theorem ScalarSolutionComparisonGenuineDualityEstimateSharpLoss.to_halfExponentSharpLoss
    {d : ℕ} [NeZero d] {C : ℝ}
    (hdual : ScalarSolutionComparisonGenuineDualityEstimateSharpLoss d C) :
    ScalarSolutionComparisonDualityEstimateHalfExponentSharpLoss d (110 * C) := by
  refine ⟨mul_nonneg (by norm_num) hdual.1, ?_⟩
  intro Q sigma0 w F s j hsigma0 hs hs_lt_one hF hw hsol
  let t : ℝ := s / 2
  let K : ℝ := 1 + Real.sqrt (sharpBoundaryKernelLoss d t)
  let L : ℝ := localizedFluxDefectNegativeBesovAverageTwo Q t F j
  let Gc : Vec d → Vec d :=
    fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)
  let Gf : Vec d → Vec d :=
    fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have ht_lt_s : t < s := by
    dsimp [t]
    linarith
  have ht_lt_half : t < 1 / 2 := by
    dsimp [t]
    linarith
  have hwMem : MemVectorL2 (cubeSet Q) w :=
    memVectorL2_of_isPotentialZeroTraceOn hw
  have hGcMem : MemVectorL2 (cubeSet Q) Gc := by
    have hEll :
        IsEllipticFieldOn sigma0 sigma0 (cubeSet Q)
          (constantCoeffField (scalarMatrix (d := d) sigma0)) :=
      isEllipticFieldOn_constantCoeffField
        (measurableSet_cubeSet Q) (isEllipticMatrix_scalarMatrix hsigma0)
    simpa [Gc, constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll hwMem
  have hGfMem : MemVectorL2 (cubeSet Q) Gf := by
    simpa [Gf, Gc] using! hGcMem.add hF
  have hGc_embed :
      cubeBesovNegativeVectorSeminormTwo Q s Gc ≤
        besovExponentLossGap s t *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc := by
    have h :=
      (concreteNegativeFromDualExponentLoss_geometric d).2
        Q Gc ht_pos ht_lt_s hs_lt_one hGcMem
    simpa using h
  have hGf_embed :
      cubeBesovNegativeVectorSeminormTwo Q s Gf ≤
        besovExponentLossGap s t *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf := by
    have h :=
      (concreteNegativeFromDualExponentLoss_geometric d).2
        Q Gf ht_pos ht_lt_s hs_lt_one hGfMem
    simpa using h
  have hgap_nonneg : 0 ≤ besovExponentLossGap s t :=
    besovExponentLossGap_nonneg ht_pos ht_lt_s
  have hgenuine :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc +
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf ≤
        C * K * t⁻¹ * L := by
    simpa [Gc, Gf, K, L, t] using
      hdual.2 Q sigma0 w F (t := t) j
        hsigma0 ht_pos ht_lt_half hF hw hsol
  have hraw :
      cubeBesovNegativeVectorSeminormTwo Q s Gc +
          cubeBesovNegativeVectorSeminormTwo Q s Gf ≤
        C * K * t⁻¹ * besovExponentLossGap s t * L := by
    calc
      cubeBesovNegativeVectorSeminormTwo Q s Gc +
          cubeBesovNegativeVectorSeminormTwo Q s Gf
          ≤ besovExponentLossGap s t *
              cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc +
            besovExponentLossGap s t *
              cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf :=
            add_le_add hGc_embed hGf_embed
      _ =
          besovExponentLossGap s t *
            (cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc +
              cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf) := by
          ring
      _ ≤ besovExponentLossGap s t * (C * K * t⁻¹ * L) := by
          exact mul_le_mul_of_nonneg_left hgenuine hgap_nonneg
      _ = C * K * t⁻¹ * besovExponentLossGap s t * L := by
          ring
  have hgap :
      besovExponentLossGap s (s / 2) ≤ 55 * (s⁻¹) ^ (2 : ℕ) :=
    besovExponentLossGap_half_le_fiftyFive_inv_sq hs hs_lt_one
  have hinv_half : (s / 2)⁻¹ = 2 * s⁻¹ := by
    field_simp [hs.ne']
  have hinv_nonneg : 0 ≤ 2 * s⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hs.le)
  have hfactor :
      (s / 2)⁻¹ * besovExponentLossGap s (s / 2) ≤
        110 * (s⁻¹) ^ (3 : ℕ) := by
    calc
      (s / 2)⁻¹ * besovExponentLossGap s (s / 2)
          = (2 * s⁻¹) * besovExponentLossGap s (s / 2) := by rw [hinv_half]
      _ ≤ (2 * s⁻¹) * (55 * (s⁻¹) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hgap hinv_nonneg
      _ = 110 * (s⁻¹) ^ (3 : ℕ) := by ring
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hCK_nonneg : 0 ≤ C * K := mul_nonneg hdual.1 hK_nonneg
  have hL_nonneg : 0 ≤ L := by
    dsimp [L, t]
    exact localizedFluxDefectNegativeBesovAverageTwo_nonneg Q (s / 2) F j
  have htail :
      C * K * t⁻¹ * besovExponentLossGap s t * L ≤
        (110 * C) * K * (s⁻¹) ^ (3 : ℕ) * L := by
    have hcoeff :
        C * K * ((s / 2)⁻¹ * besovExponentLossGap s (s / 2)) ≤
          C * K * (110 * (s⁻¹) ^ (3 : ℕ)) :=
      mul_le_mul_of_nonneg_left hfactor hCK_nonneg
    calc
      C * K * t⁻¹ * besovExponentLossGap s t * L
          = C * K * ((s / 2)⁻¹ * besovExponentLossGap s (s / 2)) * L := by
            dsimp [t]
            ring
      _ ≤ C * K * (110 * (s⁻¹) ^ (3 : ℕ)) * L :=
            mul_le_mul_of_nonneg_right hcoeff hL_nonneg
      _ = (110 * C) * K * (s⁻¹) ^ (3 : ℕ) * L := by ring
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
        cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)
        = cubeBesovNegativeVectorSeminormTwo Q s Gc +
            cubeBesovNegativeVectorSeminormTwo Q s Gf := by rfl
    _ ≤ C * K * t⁻¹ * besovExponentLossGap s t * L := hraw
    _ ≤ (110 * C) * K * (s⁻¹) ^ (3 : ℕ) * L := htail
    _ =
        (110 * C) * (1 + Real.sqrt (sharpBoundaryKernelLoss d (s / 2))) *
          (s⁻¹) ^ (3 : ℕ) *
            localizedFluxDefectNegativeBesovAverageTwo Q (s / 2) F j := by
        dsimp [K, L, t]

/-- Keep the two exponents exposed and absorb the sharp-boundary and
dual-to-circ geometric factors into the note-facing
`s^{-1} t^{-2} (1/2 - t)^{-1}` loss. -/
theorem ScalarSolutionComparisonGenuineDualityEstimateSharpLoss.to_exponentLoss
    {d : ℕ} [NeZero d] {C : ℝ}
    (hdual : ScalarSolutionComparisonGenuineDualityEstimateSharpLoss d C) :
    ScalarSolutionComparisonDualityEstimateExponentLoss d
      (110 * sharpBoundaryKernelNoteConstant d * C) := by
  refine
    ⟨mul_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (110 : ℝ))
        (sharpBoundaryKernelNoteConstant_nonneg d)) hdual.1, ?_⟩
  intro Q sigma0 w F s t j hsigma0 hs ht hts hs_lt_one hF hw hsol
  let K : ℝ := 1 + Real.sqrt (sharpBoundaryKernelLoss d t)
  let H : ℝ := ((1 / 2 : ℝ) - t)⁻¹
  let S : ℝ := sharpBoundaryKernelNoteConstant d
  let L : ℝ := localizedFluxDefectNegativeBesovAverageTwo Q t F j
  let Gc : Vec d → Vec d :=
    fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)
  let Gf : Vec d → Vec d :=
    fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x
  have ht_lt_s : t < s := by linarith
  have ht_lt_half : t < 1 / 2 := by linarith
  have hwMem : MemVectorL2 (cubeSet Q) w :=
    memVectorL2_of_isPotentialZeroTraceOn hw
  have hGcMem : MemVectorL2 (cubeSet Q) Gc := by
    have hEll :
        IsEllipticFieldOn sigma0 sigma0 (cubeSet Q)
          (constantCoeffField (scalarMatrix (d := d) sigma0)) :=
      isEllipticFieldOn_constantCoeffField
        (measurableSet_cubeSet Q) (isEllipticMatrix_scalarMatrix hsigma0)
    simpa [Gc, constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll hwMem
  have hGfMem : MemVectorL2 (cubeSet Q) Gf := by
    simpa [Gf, Gc] using! hGcMem.add hF
  have hGc_embed :
      cubeBesovNegativeVectorSeminormTwo Q s Gc ≤
        besovExponentLossGap s t *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc := by
    have h :=
      (concreteNegativeFromDualExponentLoss_geometric d).2
        Q Gc ht ht_lt_s hs_lt_one hGcMem
    simpa using h
  have hGf_embed :
      cubeBesovNegativeVectorSeminormTwo Q s Gf ≤
        besovExponentLossGap s t *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf := by
    have h :=
      (concreteNegativeFromDualExponentLoss_geometric d).2
        Q Gf ht ht_lt_s hs_lt_one hGfMem
    simpa using h
  have hgap_nonneg : 0 ≤ besovExponentLossGap s t :=
    besovExponentLossGap_nonneg ht ht_lt_s
  have hgenuine :
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc +
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf ≤
        C * K * t⁻¹ * L := by
    simpa [Gc, Gf, K, L] using
      hdual.2 Q sigma0 w F (t := t) j
        hsigma0 ht ht_lt_half hF hw hsol
  have hraw :
      cubeBesovNegativeVectorSeminormTwo Q s Gc +
          cubeBesovNegativeVectorSeminormTwo Q s Gf ≤
        C * K * t⁻¹ * besovExponentLossGap s t * L := by
    calc
      cubeBesovNegativeVectorSeminormTwo Q s Gc +
          cubeBesovNegativeVectorSeminormTwo Q s Gf
          ≤ besovExponentLossGap s t *
              cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc +
            besovExponentLossGap s t *
              cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf :=
            add_le_add hGc_embed hGf_embed
      _ =
          besovExponentLossGap s t *
            (cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gc +
              cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t Gf) := by
          ring
      _ ≤ besovExponentLossGap s t * (C * K * t⁻¹ * L) := by
          exact mul_le_mul_of_nonneg_left hgenuine hgap_nonneg
      _ = C * K * t⁻¹ * besovExponentLossGap s t * L := by
          ring
  have hK_le : K ≤ S * H := by
    dsimp [K, S, H]
    exact one_add_sqrt_sharpBoundaryKernelLoss_le_noteConstant ht ht_lt_half
  have hgap_le :
      besovExponentLossGap s t ≤ 110 * s⁻¹ * t⁻¹ :=
    besovExponentLossGap_le_note hs ht hts hs_lt_one
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact sharpBoundaryKernelNoteConstant_nonneg d
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    exact inv_nonneg.mpr (by linarith : 0 ≤ (1 / 2 : ℝ) - t)
  have ht_inv_nonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact localizedFluxDefectNegativeBesovAverageTwo_nonneg Q t F j
  have hfactor :
      K * t⁻¹ * besovExponentLossGap s t ≤
        S * H * t⁻¹ * (110 * s⁻¹ * t⁻¹) := by
    have hKt :
        K * t⁻¹ ≤ (S * H) * t⁻¹ :=
      mul_le_mul_of_nonneg_right hK_le ht_inv_nonneg
    have hSHt_nonneg : 0 ≤ (S * H) * t⁻¹ :=
      mul_nonneg (mul_nonneg hS_nonneg hH_nonneg) ht_inv_nonneg
    calc
      K * t⁻¹ * besovExponentLossGap s t
          = (K * t⁻¹) * besovExponentLossGap s t := by ring
      _ ≤ ((S * H) * t⁻¹) * besovExponentLossGap s t :=
          mul_le_mul_of_nonneg_right hKt hgap_nonneg
      _ ≤ ((S * H) * t⁻¹) * (110 * s⁻¹ * t⁻¹) :=
          mul_le_mul_of_nonneg_left hgap_le hSHt_nonneg
      _ = S * H * t⁻¹ * (110 * s⁻¹ * t⁻¹) := by ring
  have htail :
      C * K * t⁻¹ * besovExponentLossGap s t * L ≤
        (110 * S * C) * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * H * L := by
    calc
      C * K * t⁻¹ * besovExponentLossGap s t * L
          = C * (K * t⁻¹ * besovExponentLossGap s t) * L := by ring
      _ ≤ C * (S * H * t⁻¹ * (110 * s⁻¹ * t⁻¹)) * L := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfactor hdual.1) hL_nonneg
      _ = (110 * S * C) * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * H * L := by
            ring
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) +
        cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)
        = cubeBesovNegativeVectorSeminormTwo Q s Gc +
            cubeBesovNegativeVectorSeminormTwo Q s Gf := by rfl
    _ ≤ C * K * t⁻¹ * besovExponentLossGap s t * L := hraw
    _ ≤ (110 * S * C) * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * H * L := htail
    _ =
        (110 * sharpBoundaryKernelNoteConstant d * C) * s⁻¹ *
          (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ *
            localizedFluxDefectNegativeBesovAverageTwo Q t F j := by
        dsimp [S, H, L]

/-- Use the sharp-loss half-exponent scalar-background duality estimate on a
comparison pair. -/
theorem solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimateHalfExponentSharpLoss
    {d : ℕ} [NeZero d] {C : ℝ}
    (hduality : ScalarSolutionComparisonDualityEstimateHalfExponentSharpLoss d C)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (gradU gradV : Vec d → Vec d) {s : ℝ} (j : ℕ)
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hF :
      MemVectorL2 (cubeSet Q)
        (fluxDefect a (scalarMatrix (d := d) sigma0) gradU))
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a
        (scalarMatrix (d := d) sigma0) gradU gradV) :
    solutionComparisonNegativeBesovLhs Q s a (scalarMatrix (d := d) sigma0) gradU gradV ≤
      C * (1 + Real.sqrt (sharpBoundaryKernelLoss d (s / 2))) *
        (s⁻¹) ^ (3 : ℕ) *
          localizedFluxDefectNegativeBesovAverageTwo Q (s / 2)
            (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j := by
  have hbound :=
    hduality.2 Q sigma0 (fun x => gradU x - gradV x)
      (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j
      hsigma0 hs_pos hs_lt_one hF hcomparison.2 hcomparison.comparisonPair_solenoidal
  rwa [solutionComparisonNegativeBesovLhs_eq_comparisonPair]

/-- Use the two-exponent scalar-background duality estimate on a comparison
pair. -/
theorem solutionComparisonNegativeBesovLhs_le_of_scalarSolutionComparisonDualityEstimateExponentLoss
    {d : ℕ} [NeZero d] {C : ℝ}
    (hduality : ScalarSolutionComparisonDualityEstimateExponentLoss d C)
    (Q : TriadicCube d) (a : CoeffField d) (sigma0 : ℝ)
    (gradU gradV : Vec d → Vec d) {s t : ℝ} (j : ℕ)
    (hsigma0 : 0 < sigma0)
    (hs_pos : 0 < s) (ht_pos : 0 < t) (hts : t < s / 2) (hs_lt_one : s < 1)
    (hF :
      MemVectorL2 (cubeSet Q)
        (fluxDefect a (scalarMatrix (d := d) sigma0) gradU))
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a
        (scalarMatrix (d := d) sigma0) gradU gradV) :
    solutionComparisonNegativeBesovLhs Q s a (scalarMatrix (d := d) sigma0) gradU gradV ≤
      C * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ *
          localizedFluxDefectNegativeBesovAverageTwo Q t
            (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j := by
  have hbound :=
    hduality.2 Q sigma0 (fun x => gradU x - gradV x)
      (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j
      hsigma0 hs_pos ht_pos hts hs_lt_one hF hcomparison.2
      hcomparison.comparisonPair_solenoidal
  rwa [solutionComparisonNegativeBesovLhs_eq_comparisonPair]

end

end Homogenization
