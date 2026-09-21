/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.MatrixAverageGeometric
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.TraceBudgetAlgebra

/-! # Trace Average Estimate -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section54.VarianceBoundGoodScale

/-- Constant multiplying the geometric matrix-average contribution in the
concrete trace-`J` square estimate. -/
noncomputable def normalizedTraceJAverageGeometricConst
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  8 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
    normalizedMatrixAverageGeometricConst hP4

/-- Constant multiplying `(Theta_m - 1)^2` in the concrete trace-`J` square
estimate. -/
noncomputable def normalizedTraceJAverageThetaConst (d : ℕ) : ℝ :=
  2 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)

theorem normalizedBlockJTraceAverage_eq_trace_fluctuation_add_theta_gap
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {child parent : ℕ}
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    let Q : TriadicCube d := originCube d (parent : ℤ)
    let j : ℕ := parent - child
    let M : FullBlockMat d :=
      descendantsAverageNormalizedFluctuationMatrix
        hP hStruct (child : ℤ) Q j a
    let θ : ℝ := thetaAtScale hP hStruct (child : ℤ)
    normalizedBlockJTraceAverage hP hStruct (child : ℤ) Q j a =
      ((1 + θ) / 2) * Ch02.fullBlockTrace M +
        ((Fintype.card (BlockCoord d) : ℝ) / 2) * (θ - 1) := by
  intro Q j M θ
  classical
  let b := hP.barSigmaAtScale hStruct (child : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (child : ℤ)
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let T : FullBlockMat d := Matrix.diagonal (scalarFullBlockSqrtDiag b c)
  let Aavg : BlockMat d :=
    descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun)
  let Abar : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (child : ℤ))
  have hb : 0 < b := by
    simpa [b] using
      Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 child
  have hc : 0 < c := by
    simpa [c] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 child
  have hTraceAverage :
      normalizedBlockJTraceAverage hP hStruct (child : ℤ) Q j a =
        blockJTraceAverageWithNormalizers D T Q j a := by
    simpa [D, T, b, c] using
      normalizedBlockJTraceAverage_eq_blockJTraceAverageWithNormalizers
        hP hStruct (child : ℤ) Q j a
  have hBudget :
      blockJTraceAverageWithNormalizers D T Q j a =
        fullBlockJTraceBudgetWithNormalizers D T Aavg := by
    simpa [Aavg] using
      blockJTraceAverageWithNormalizers_eq_traceBudget_descendantsAverageBlockMat
        ha D T Q j
  have hBudgetFormula :
      fullBlockJTraceBudgetWithNormalizers D T Aavg =
        ((1 + θ) / 2) *
            Ch02.fullBlockTrace (D * toFullBlockMat Aavg * D) -
          (Fintype.card (BlockCoord d) : ℝ) := by
    simpa [D, T, θ, thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b, c] using
      fullBlockJTraceBudgetWithNormalizers_normalized_eq_trace
        (d := d) hb hc Aavg
  have hFluct :
      M = D * (toFullBlockMat Aavg - Abar) * D := by
    simpa [M, Q, j, D, b, c, Aavg, Abar] using
      descendantsAverageNormalizedFluctuationMatrix_eq_diagonal_average_sub_annealed
        hP hStruct (child : ℤ) Q j a
  have hAnnealed : D * Abar * D = 1 := by
    simpa [D, Abar, b, c] using
      normalizedScalarAnnealedBlockMatrix_self_eq_one hP hStruct hP4 child
  have hAvg_eq : D * toFullBlockMat Aavg * D = M + 1 := by
    calc
      D * toFullBlockMat Aavg * D =
          D * (toFullBlockMat Aavg - Abar) * D + D * Abar * D := by
            noncomm_ring
      _ = M + 1 := by rw [← hFluct, hAnnealed]
  have hTrace :
      Ch02.fullBlockTrace (D * toFullBlockMat Aavg * D) =
        Ch02.fullBlockTrace M + (Fintype.card (BlockCoord d) : ℝ) := by
    rw [hAvg_eq]
    unfold Ch02.fullBlockTrace
    simp [Matrix.add_apply, Finset.sum_add_distrib]
  calc
    normalizedBlockJTraceAverage hP hStruct (child : ℤ) Q j a
        = blockJTraceAverageWithNormalizers D T Q j a := hTraceAverage
    _ = fullBlockJTraceBudgetWithNormalizers D T Aavg := hBudget
    _ =
        ((1 + θ) / 2) *
            Ch02.fullBlockTrace (D * toFullBlockMat Aavg * D) -
          (Fintype.card (BlockCoord d) : ℝ) := hBudgetFormula
    _ =
        ((1 + θ) / 2) *
            (Ch02.fullBlockTrace M + (Fintype.card (BlockCoord d) : ℝ)) -
          (Fintype.card (BlockCoord d) : ℝ) := by rw [hTrace]
    _ =
        ((1 + θ) / 2) * Ch02.fullBlockTrace M +
          ((Fintype.card (BlockCoord d) : ℝ) / 2) * (θ - 1) := by ring

theorem normalizedBlockJTraceAverageSq_le_matrix_average_add_thetaSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {child parent : ℕ}
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    normalizedBlockJTraceAverageSq hP hStruct (child : ℤ)
        (originCube d (parent : ℤ)) (parent - child) a ≤
      8 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
          descendantsAverageNormalizedFluctuationOperatorNormSq
            hP hStruct (child : ℤ) (originCube d (parent : ℤ))
              (parent - child) a +
        normalizedTraceJAverageThetaConst d *
          (thetaAtScale hP hStruct (child : ℤ) - 1) ^ (2 : ℕ) := by
  classical
  let Q : TriadicCube d := originCube d (parent : ℤ)
  let j : ℕ := parent - child
  let M : FullBlockMat d :=
    descendantsAverageNormalizedFluctuationMatrix
      hP hStruct (child : ℤ) Q j a
  let θ : ℝ := thetaAtScale hP hStruct (child : ℤ)
  let card : ℝ := Fintype.card (BlockCoord d)
  let opSq : ℝ :=
    descendantsAverageNormalizedFluctuationOperatorNormSq
      hP hStruct (child : ℤ) Q j a
  let coeff : ℝ := (1 + θ) / 2
  let x : ℝ := coeff * Ch02.fullBlockTrace M
  let y : ℝ := (card / 2) * (θ - 1)
  let J : ℝ := normalizedBlockJTraceAverage hP hStruct (child : ℤ) Q j a
  have hJ : J = x + y := by
    simpa [J, x, y, coeff, M, θ, Q, j, card] using
      normalizedBlockJTraceAverage_eq_trace_fluctuation_add_theta_gap
        hP hStruct hP4 ha
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using
      Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 child
  have hθ_two : θ ≤ 2 := by
    simpa [θ] using
      thetaAtScale_le_two_of_widetildeThetaAtScale_zero_le_two
        hP hStruct hP4 hsmall child
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    nlinarith
  have hcoeff_le_two : coeff ≤ 2 := by
    dsimp [coeff]
    nlinarith
  have hcoeff_sq_le_four : coeff ^ (2 : ℕ) ≤ 4 := by
    have h := pow_le_pow_left₀ hcoeff_nonneg hcoeff_le_two 2
    norm_num at h
    exact h
  have htrace_bound :
      Ch02.fullBlockTrace M ^ (2 : ℕ) ≤ card ^ (2 : ℕ) * opSq := by
    simpa [M, opSq, Q, j, card, descendantsAverageNormalizedFluctuationOperatorNormSq] using
      fullBlockTrace_sq_le_card_sq_operatorNormSq M
  have hx_bound :
      2 * x ^ (2 : ℕ) ≤ 8 * card ^ (2 : ℕ) * opSq := by
    have htrace_sq_nonneg : 0 ≤ Ch02.fullBlockTrace M ^ (2 : ℕ) :=
      sq_nonneg _
    have hx_sq :
        x ^ (2 : ℕ) ≤ 4 * Ch02.fullBlockTrace M ^ (2 : ℕ) := by
      calc
        x ^ (2 : ℕ) =
            coeff ^ (2 : ℕ) * Ch02.fullBlockTrace M ^ (2 : ℕ) := by
              dsimp [x]
              ring
        _ ≤ 4 * Ch02.fullBlockTrace M ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hcoeff_sq_le_four htrace_sq_nonneg
    calc
      2 * x ^ (2 : ℕ) ≤ 2 * (4 * Ch02.fullBlockTrace M ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hx_sq (by norm_num)
      _ = 8 * Ch02.fullBlockTrace M ^ (2 : ℕ) := by ring
      _ ≤ 8 * (card ^ (2 : ℕ) * opSq) :=
        mul_le_mul_of_nonneg_left htrace_bound (by norm_num)
      _ = 8 * card ^ (2 : ℕ) * opSq := by ring
  have hy_bound :
      2 * y ^ (2 : ℕ) ≤
        normalizedTraceJAverageThetaConst d * (θ - 1) ^ (2 : ℕ) := by
    have hnonneg :
        0 ≤ card ^ (2 : ℕ) * (θ - 1) ^ (2 : ℕ) :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    dsimp [normalizedTraceJAverageThetaConst, y, card]
    nlinarith
  have hsplit : (x + y) ^ (2 : ℕ) ≤ 2 * x ^ (2 : ℕ) + 2 * y ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - y)]
  calc
    normalizedBlockJTraceAverageSq hP hStruct (child : ℤ) Q j a
        = J ^ (2 : ℕ) := by rfl
    _ = (x + y) ^ (2 : ℕ) := by rw [hJ]
    _ ≤ 2 * x ^ (2 : ℕ) + 2 * y ^ (2 : ℕ) := hsplit
    _ ≤
        8 * card ^ (2 : ℕ) * opSq +
          normalizedTraceJAverageThetaConst d * (θ - 1) ^ (2 : ℕ) :=
        add_le_add hx_bound hy_bound
    _ =
        8 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
            descendantsAverageNormalizedFluctuationOperatorNormSq
              hP hStruct (child : ℤ) (originCube d (parent : ℤ))
                (parent - child) a +
          normalizedTraceJAverageThetaConst d *
            (thetaAtScale hP hStruct (child : ℤ) - 1) ^ (2 : ℕ) := by
        simp [Q, j, opSq, θ, card]

theorem normalizedBlockJTraceAverageSq_integral_le_geometric_add_thetaSq_of_smallContrast
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {child parent : ℕ} (hchild_parent : child ≤ parent) :
    ∫ a,
        normalizedBlockJTraceAverageSq hP hStruct (child : ℤ)
          (originCube d (parent : ℤ)) (parent - child) a ∂P ≤
      normalizedTraceJAverageGeometricConst hP4 *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) +
        normalizedTraceJAverageThetaConst d *
          (thetaAtScale hP hStruct (child : ℤ) - 1) ^ (2 : ℕ) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (parent : ℤ)
  let j : ℕ := parent - child
  let opSq : RegCoeffField d → ℝ :=
    descendantsAverageNormalizedFluctuationOperatorNormSq
      hP hStruct (child : ℤ) Q j
  let gapSq : ℝ := (thetaAtScale hP hStruct (child : ℤ) - 1) ^ (2 : ℕ)
  let traceConst : ℝ := 8 * (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let thetaConst : ℝ := normalizedTraceJAverageThetaConst d
  have hleft_int :
      Integrable
        (normalizedBlockJTraceAverageSq hP hStruct (child : ℤ) Q j) P := by
    simpa [Q, j] using
      integrable_normalizedBlockJTraceAverageSq_from_P4_of_stationary
        hP hStruct hP4 child parent child hchild_parent
  have hop_int : Integrable opSq P := by
    simpa [opSq, Q, j] using
      integrable_descendantsAverageNormalizedFluctuationOperatorNormSq_from_P4_of_stationary
        hP hStruct hP4 child parent child hchild_parent
  have hright_int :
      Integrable (fun a : RegCoeffField d => traceConst * opSq a + thetaConst * gapSq) P :=
    (hop_int.const_mul traceConst).add (integrable_const (thetaConst * gapSq))
  have hpoint :
      (fun a : RegCoeffField d =>
        normalizedBlockJTraceAverageSq hP hStruct (child : ℤ) Q j a)
        ≤ᵐ[P]
      fun a : RegCoeffField d => traceConst * opSq a + thetaConst * gapSq := by
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    simpa [traceConst, thetaConst, gapSq, opSq, Q, j] using
      normalizedBlockJTraceAverageSq_le_matrix_average_add_thetaSq
        hP hStruct hP4 hsmall ha
  have hmono :
      ∫ a, normalizedBlockJTraceAverageSq hP hStruct (child : ℤ) Q j a ∂P ≤
        ∫ a, traceConst * opSq a + thetaConst * gapSq ∂P :=
    integral_mono_ae hleft_int hright_int hpoint
  have hright_eval :
      ∫ a, traceConst * opSq a + thetaConst * gapSq ∂P =
        traceConst * ∫ a, opSq a ∂P + thetaConst * gapSq := by
    rw [integral_add (hop_int.const_mul traceConst)
      (integrable_const (thetaConst * gapSq))]
    rw [integral_const_mul]
    rw [integral_const]
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have hop_bound :
      ∫ a, opSq a ∂P ≤
        normalizedMatrixAverageGeometricConst hP4 *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) := by
    simpa [opSq, Q, j] using
      descendantsAverageNormalizedFluctuationOperatorNormSq_integral_le_geometric_of_smallContrast
        hP hStruct hP4 hsmall hchild_parent
  have htraceConst_nonneg : 0 ≤ traceConst := by
    dsimp [traceConst]
    nlinarith [sq_nonneg (Fintype.card (BlockCoord d) : ℝ)]
  calc
    ∫ a,
        normalizedBlockJTraceAverageSq hP hStruct (child : ℤ)
          (originCube d (parent : ℤ)) (parent - child) a ∂P
        =
      ∫ a, normalizedBlockJTraceAverageSq hP hStruct (child : ℤ) Q j a ∂P := by
        rfl
    _ ≤ ∫ a, traceConst * opSq a + thetaConst * gapSq ∂P := hmono
    _ = traceConst * ∫ a, opSq a ∂P + thetaConst * gapSq := hright_eval
    _ ≤
        traceConst *
            (normalizedMatrixAverageGeometricConst hP4 *
              Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ))) +
          thetaConst * gapSq :=
        add_le_add
          (mul_le_mul_of_nonneg_left hop_bound htraceConst_nonneg)
          le_rfl
    _ =
        normalizedTraceJAverageGeometricConst hP4 *
            Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) +
          normalizedTraceJAverageThetaConst d *
            (thetaAtScale hP hStruct (child : ℤ) - 1) ^ (2 : ℕ) := by
        simp [normalizedTraceJAverageGeometricConst, traceConst, thetaConst, gapSq]
        ring

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
