/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-! # Bounded Off Diagonal -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Bounded double-angle tangent reduction

This leaf supplies the analytic conversion needed by the bounded
`tan 2Theta` theorem. In the quarter-acute regime, coercivity of the extended
double-angle cosine controls its inverse. Consequently a weighted
`sin 2Theta` estimate with the same cosine factor immediately yields the
sharp tangent estimate.

The operator in this file is the implemented complex operator-angle object
`directedTanTwoAngleOperatorC`. The scalar-generic compatibility object is kept out
of this leaf until it is connected to the complex and real constructions.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem quarterAcute_doubleCosineConstant_pos
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    0 < 1 - 2 * U.directedProjectionGap V ^ 2 := by
  have hglt : U.directedProjectionGap V < Real.sqrt 2 / 2 :=
    lt_of_le_of_lt (Submodule.directedProjectionGap_le_projectionGap U V) hquarter
  have hg0 : 0 ≤ U.directedProjectionGap V := by
    rw [show U.directedProjectionGap V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

variable [CompleteSpace E]

/-- Pointwise norm bound for the inverse extended double-angle cosine. -/
theorem norm_cosTwoAngleExtendedCEquiv_symm_apply_le
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) (y : E) :
    ‖(cosTwoAngleExtendedCEquiv U V hquarter).symm y‖ ≤
      (1 - 2 * U.directedProjectionGap V ^ 2)⁻¹ * ‖y‖ := by
  let c : ℝ := 1 - 2 * U.directedProjectionGap V ^ 2
  have hcpos : 0 < c := quarterAcute_doubleCosineConstant_pos U V hquarter
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith [sq_nonneg (U.directedProjectionGap V)]
  have hcoerU : ∀ x ∈ U,
      c * ‖x‖ ≤ ‖cosTwoAngleOperatorC U V x‖ := by
    intro x hx
    exact norm_cosTwoAngleOperatorC_apply_ge U V hx
  have hlow := norm_add_starProjection_orthogonal_apply_ge U
    (fun x hx => cosTwoAngleOperatorC_apply_mem U V hx)
    (fun z hz => cosTwoAngleOperatorC_apply_eq_zero_of_mem_orthogonal U V hz)
    hcpos.le hc1 hcoerU
  have hcoer :
      c * ‖(cosTwoAngleExtendedCEquiv U V hquarter).symm y‖ ≤
        ‖cosTwoAngleExtendedC U V
          ((cosTwoAngleExtendedCEquiv U V hquarter).symm y)‖ := by
    simpa only [cosTwoAngleExtendedC] using
      hlow ((cosTwoAngleExtendedCEquiv U V hquarter).symm y)
  have happ : cosTwoAngleExtendedC U V
      ((cosTwoAngleExtendedCEquiv U V hquarter).symm y) = y :=
    (cosTwoAngleExtendedCEquiv U V hquarter).apply_symm_apply y
  rw [happ] at hcoer
  calc
    ‖(cosTwoAngleExtendedCEquiv U V hquarter).symm y‖ =
        c⁻¹ * (c * ‖(cosTwoAngleExtendedCEquiv U V hquarter).symm y‖) :=
      (inv_mul_cancel_left₀ hcpos.ne' _).symm
    _ ≤ c⁻¹ * ‖y‖ :=
      mul_le_mul_of_nonneg_left hcoer (inv_nonneg.mpr hcpos.le)

/-- Operator-norm bound for the inverse extended double-angle cosine. -/
theorem norm_cosTwoAngleExtendedCEquiv_symm_le
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    ‖(cosTwoAngleExtendedCEquiv U V hquarter).symm.toContinuousLinearMap‖ ≤
      (1 - 2 * U.directedProjectionGap V ^ 2)⁻¹ := by
  have hcpos := quarterAcute_doubleCosineConstant_pos U V hquarter
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hcpos.le) ?_
  intro y
  exact norm_cosTwoAngleExtendedCEquiv_symm_apply_le U V hquarter y

/-- The double-angle tangent norm is controlled by the double-angle sine norm
and the quarter-acute cosine denominator. -/
theorem norm_directedTanTwoAngleOperatorC_le_sine_div_doubleCosine
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤
      ‖directedSinTwoAngleOperatorC U V‖ /
        (1 - 2 * U.directedProjectionGap V ^ 2) := by
  have hinv := norm_cosTwoAngleExtendedCEquiv_symm_le U V hquarter
  calc
    ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤
        ‖directedSinTwoAngleOperatorC U V‖ *
          ‖(cosTwoAngleExtendedCEquiv U V hquarter).symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖directedSinTwoAngleOperatorC U V‖ *
        (1 - 2 * U.directedProjectionGap V ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = ‖directedSinTwoAngleOperatorC U V‖ /
        (1 - 2 * U.directedProjectionGap V ^ 2) := by
      rw [div_eq_mul_inv]

/-- A weighted double-angle sine estimate converts directly into the
corresponding tangent estimate. This is the scalar endpoint consumed by the
bounded off-diagonal theorem. -/
theorem norm_directedTanTwoAngleOperatorC_le_of_weighted_sine
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V)
    {d r : ℝ} (hd : 0 < d)
    (hweighted :
      d * ‖directedSinTwoAngleOperatorC U V‖ ≤
        r * (1 - 2 * U.directedProjectionGap V ^ 2)) :
    ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤ r / d := by
  have hcpos := quarterAcute_doubleCosineConstant_pos U V hquarter
  calc
    ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤
        ‖directedSinTwoAngleOperatorC U V‖ /
          (1 - 2 * U.directedProjectionGap V ^ 2) :=
      norm_directedTanTwoAngleOperatorC_le_sine_div_doubleCosine U V hquarter
    _ ≤ r / d := by
      rw [div_le_div_iff₀ hcpos hd]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hweighted

/-- Specialization of the weighted-sine conversion to the perturbation
constant appearing in the bounded off-diagonal theorem. -/
theorem tanTwoTheta_offDiagonalC_of_weighted_sine
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V)
    {d : ℝ} (hd : 0 < d) (H : E →L[ℂ] E)
    (hweighted :
      d * ‖directedSinTwoAngleOperatorC U V‖ ≤
        (2 * ‖H‖) * (1 - 2 * U.directedProjectionGap V ^ 2)) :
    ‖directedTanTwoAngleOperatorC U V hquarter‖ ≤ 2 * ‖H‖ / d :=
  norm_directedTanTwoAngleOperatorC_le_of_weighted_sine U V hquarter hd hweighted

end DavisKahanExt
end TauCeti
