/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionMetricBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCoefficientGevrey

/-! Quantitative bounds for the actual inverse metric and its first spatial
and time derivatives, from the prescribed deformation jets. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketCylinderField
  EulerAllOrderCorrectionData EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (R C0 C1 : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C0 * majorant R
      0
      n)
  (hF1 : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C1 * majorant
      R
      0 n)

include hR hC0 hF in
theorem inverseMetricCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (inverseMetricCoefficient D).path) a‖ ≤
      (3*C0*C0)*majorant R 0 n := by
  have hf := frameCoefficient_bound D R C0 hR hC0 hF
  exact MatrixCoefficient.comp_bound (frameCoefficient D).adjoint (frameCoefficient D)
    R C0 C0 hR hC0 hC0 ((frameCoefficient D).adjoint_bound R C0 hf) hf n a

include hR hC0 hF in
theorem inverseMetricFirstBound_le_source : inverseMetricFirstBound D ≤ 3*C0*C0*R := by
  have h := inverseMetricCoefficient_bound D R C0 hR hC0 hF 1 0
  simpa only [inverseMetricFirstBound,majorant,Nat.add_zero,Nat.factorial_one,
    Nat.cast_one,pow_one,one_pow,mul_one] using h

include hC0 hF in
theorem framePath_norm_le_source : ‖D.F.field‖ ≤ C0 := by
  apply (ContinuousMap.norm_le _ hC0).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le hC0).mpr
  intro x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] using hF 0 t x

include hC1 hF1 in
theorem frameTimePath_norm_le_source : ‖D.F₁.field‖ ≤ C1 := by
  apply (ContinuousMap.norm_le _ hC1).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le hC1).mpr
  intro x
  simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
    Nat.cast_one,pow_zero,one_pow,mul_one] using hF1 0 t x

include hC0 hF in
theorem inverseMetricBound_le_source : inverseMetricBound D ≤ C0^2 := by
  have h0 := framePath_norm_le_source D R C0 hC0 hF
  exact (inverseMetricBound_le D).trans (pow_le_pow_left₀ (norm_nonneg _) h0 2)

include hC0 hC1 hF hF1 in
theorem inverseMetricTimeBound_le_source : inverseMetricTimeBound D ≤ 2*C0*C1 := by
  have h0 := framePath_norm_le_source D R C0 hC0 hF
  have h1 := frameTimePath_norm_le_source D R C1 hC1 hF1
  exact (inverseMetricTimeBound_le D).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left h0 (by norm_num)) h1 (norm_nonneg _) (by positivity))

include hR hC0 hF in
theorem sourceMetricBudget_first_le_source (P : ℝ) [Fact (0 < P)]
    (κ : ℝ) (hκ : |κ| ≤ 1) (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).first ≤ 3*C0*C0*R :=
  inverseMetricFirstBound_le_source D R C0 hR hC0 hF

end EulerPacketCorrectionCoefficients
