/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexEnergy
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.ZeroDirichletEnergy

/-! # RHSConstant Apex Zero Dirichlet Energy -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Zero-Dirichlet energy input for the one-cube RHS coarse-flux response apex

This leaf records the zero-trace energy envelope and the Poincare scalar
budget used by the corrected zero-Dirichlet apex route.
-/

open scoped BigOperators ENNReal

/--
Displayed Poincare scalar budget after the zero-trace energy envelope has
been inserted.
-/
noncomputable def zeroTraceDirichletPoincareScalarBudget {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  (matNorm a0) ^ 2 *
      (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        zeroTraceDirichletEnergyEnvelope Q a s g) +
    (matNorm a0) ^ 2 *
      (15000 * (s⁻¹) ^ 4 *
        ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

theorem zeroTraceDirichletEnergyEnvelope_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (g : Vec d → Vec d)
    (hs : 0 < s) :
    0 ≤ zeroTraceDirichletEnergyEnvelope Q a s g := by
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hA_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have hforce_nonneg :
      0 ≤
        2 *
          |(d : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + s) *
              cubeBesovPositiveVectorSeminormTwo Q s g)| *
          Real.sqrt
            (15000 * (s⁻¹) ^ 4 *
              ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (abs_nonneg _))
        (Real.sqrt_nonneg _)
  unfold zeroTraceDirichletEnergyEnvelope
  exact add_nonneg (mul_nonneg (sq_nonneg _) hA_nonneg) hforce_nonneg

theorem zeroTraceDirichletPoincareScalarBudget_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) (hs : 0 < s) :
    0 ≤ zeroTraceDirichletPoincareScalarBudget Q a a0 s g := by
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have henergyEnvelope_nonneg :
      0 ≤ zeroTraceDirichletEnergyEnvelope Q a s g :=
    zeroTraceDirichletEnergyEnvelope_nonneg Q a s g hs
  have henergy_inner_nonneg :
      0 ≤
        250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
          (inv_nonneg.mpr hlambda_nonneg))
        henergyEnvelope_nonneg
  have hs_inv_pow_four_nonneg : 0 ≤ (s⁻¹) ^ 4 := by
    rw [show (s⁻¹) ^ 4 = ((s⁻¹) ^ 2) ^ 2 by ring]
    exact sq_nonneg _
  have hforce_inner_nonneg :
      0 ≤
        15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : 0 ≤ (15000 : ℝ)) hs_inv_pow_four_nonneg)
            (sq_nonneg ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)))
          (sq_nonneg ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))))
        (sq_nonneg (cubeBesovPositiveVectorSeminormTwo Q s g))
  unfold zeroTraceDirichletPoincareScalarBudget
  exact
    add_nonneg
      (mul_nonneg (sq_nonneg (matNorm a0)) henergy_inner_nonneg)
      (mul_nonneg (sq_nonneg (matNorm a0)) hforce_inner_nonneg)

/--
Component bounds imply the named Poincare scalar budget inequality.
-/
theorem zeroTraceDirichletPoincareScalarBudget_le_const_mul_correctionBound_sq_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d) {Benergy Bforce : ℝ}
    (henergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g) ≤
        Benergy)
    (hforce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Bforce)
    (hsum :
      Benergy + Bforce ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    zeroTraceDirichletPoincareScalarBudget Q a a0 s g ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  unfold zeroTraceDirichletPoincareScalarBudget
  nlinarith

/--
The matrix-weighted depth-zero Poincare expanded radicand is controlled by the
named zero-trace Poincare scalar budget once the correction energy is bounded
by the zero-trace energy envelope.
-/
theorem matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_zeroTraceDirichletPoincareScalarBudget_of_energy_le_envelope
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (g gradV : Vec d → Vec d)
    (hs : 0 < s)
    (henergy :
      cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g) :
    (matNorm a0) ^ 2 *
        coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV ≤
      zeroTraceDirichletPoincareScalarBudget Q a a0 s g := by
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have henergy_coeff_nonneg :
      0 ≤
        250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have henergy_inner :
      250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g :=
    mul_le_mul_of_nonneg_left henergy henergy_coeff_nonneg
  have henergy_term :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a gradV)) ≤
        (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g) :=
    mul_le_mul_of_nonneg_left henergy_inner (sq_nonneg (matNorm a0))
  unfold coarseFluxResponseRHSPoincareExpandedRadicand
    zeroTraceDirichletPoincareScalarBudget
  nlinarith

/--
Poincare square-radicand closure from the named zero-trace scalar budget.
-/
theorem matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_const_mul_correctionBound_sq_of_energy_le_envelope_of_zeroTraceDirichletPoincareScalarBudget
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C : ℝ) {s : ℝ} (g gradV : Vec d → Vec d)
    (hs : 0 < s)
    (henergy :
      cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g)
    (hbudget :
      zeroTraceDirichletPoincareScalarBudget Q a a0 s g ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    (matNorm a0) ^ 2 *
        coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 :=
  (matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_zeroTraceDirichletPoincareScalarBudget_of_energy_le_envelope
    Q a a0 g gradV hs henergy).trans hbudget

/--
Poincare square-root absorption from the zero-trace energy envelope and the
named Poincare scalar budget.
-/
theorem matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_energy_le_envelope_of_zeroTraceDirichletPoincareScalarBudget
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {C s : ℝ} (g gradV : Vec d → Vec d)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (henergy :
      cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g)
    (hbudget :
      zeroTraceDirichletPoincareScalarBudget Q a a0 s g ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV ≤
      C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  exact
    matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_radicand_le_sq
      Q a a0 g gradV hC_nonneg hs havg_nonneg hgBdd
      (matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_const_mul_correctionBound_sq_of_energy_le_envelope_of_zeroTraceDirichletPoincareScalarBudget
        Q a a0 C g gradV hs henergy hbudget)

end

end Homogenization
