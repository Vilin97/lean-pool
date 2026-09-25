/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.EndPoints

/-! # Coarse Flux Response RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public/internal coarse-flux-response RHS bridge

This file contains the terminal dimension-loss comparison for the deterministic
coarse-flux-response RHS written with the Chapter 3 public coefficient field.

## Audit tag

Claim: the deterministic public-coefficient coarse-flux-response RHS is bounded
by the Chapter 3 public RHS after the explicit dimension-square loss.

Downstream target: `CoarseFluxResponseRHS.lean` through the public
`PublicInternalBridges` import surface.  This file is bridge plumbing only and
introduces no public `*Theory` package.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

theorem coarseFluxResponseRHSBound_publicCoeffField_le_dim_sq_mul_public_of_homogenizationErrorOnCube_eq
    {d : ℕ} [NeZero d] (C : ℝ) (Q : TriadicCube d)
    (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d) {s : ℝ}
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (hC : 0 ≤ C) (hs : 0 < s)
    (hB_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (hH_nonneg :
      0 ≤ Ch02.HomogenizationErrorOnCube Q s
        Ch02.MultiscaleExponent.infinity
        (Ch02.MultiscaleExponent.finite 1) a a0.matrix)
    (herror :
      HomogenizationErrorOnCube Q s .infinity (.finite 1)
          (publicCoeffField Q a) a0.matrix =
        Ch02.HomogenizationErrorOnCube Q s
          Ch02.MultiscaleExponent.infinity
          (Ch02.MultiscaleExponent.finite 1) a a0.matrix) :
    C * _root_.Homogenization.coarseFluxResponseRHSBound Q (publicCoeffField Q a)
        a0.matrix s (forcedSolutionGradientField u) g ≤
      coarseFluxResponseWithRHSRHS (((d : ℝ) ^ 2) * C) Q a a0 s g u := by
  let D : ℝ := d
  let Mhalf : ℝ := constantCoeffMatrixNormHalf a0
  let M : ℝ := constantCoeffMatrixNorm a0
  let oldMhalf : ℝ := Real.sqrt (matNorm a0.matrix)
  let oldM : ℝ := matNorm a0.matrix
  let oldP : ℝ :=
    Real.sqrt (LambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
      (publicCoeffField Q a))
  let oldL : ℝ :=
    Real.sqrt ((lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
      (publicCoeffField Q a))⁻¹)
  let oldLinv : ℝ :=
    (lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
      (publicCoeffField Q a))⁻¹
  let P : ℝ := poincareUpperEllipticityFactor Q a (s / 2)
    (Ch02.MultiscaleExponent.finite 2)
  let L : ℝ := poincareLowerEllipticityFactor Q a (s / 2)
    (Ch02.MultiscaleExponent.finite 2)
  let Linv : ℝ :=
    Real.rpow (Ch02.lambdaSq Q (s / 2)
      (Ch02.MultiscaleExponent.finite 2) a) (-1 : ℝ)
  let H : ℝ :=
    Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
      (Ch02.MultiscaleExponent.finite 1) a a0.matrix
  let E : ℝ :=
    Real.sqrt (cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (forcedSolutionGradientField u)))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  have hs_half : 0 < s / 2 := by positivity
  have hD_one : 1 ≤ D := by
    norm_num [D, Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hD_nonneg : 0 ≤ D := le_trans zero_le_one hD_one
  have hD_le_sq : D ≤ D ^ 2 := by nlinarith [hD_one]
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hs_pow52_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hs_pow3_nonneg : 0 ≤ Real.rpow s (-3 : ℝ) :=
    Real.rpow_nonneg hs.le _
  have hMhalf_nonneg : 0 ≤ Mhalf := by
    dsimp [Mhalf, constantCoeffMatrixNormHalf]
    exact Real.rpow_nonneg (Ch02.matrixNorm_nonneg a0.matrix) _
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, constantCoeffMatrixNorm]
    exact Ch02.matrixNorm_nonneg a0.matrix
  have holdMhalf_nonneg : 0 ≤ oldMhalf := by simp [oldMhalf]
  have holdM_nonneg : 0 ≤ oldM := by
    dsimp [oldM]
    exact matNorm_nonneg a0.matrix
  have holdP_nonneg : 0 ≤ oldP := by simp [oldP]
  have holdL_nonneg : 0 ≤ oldL := by simp [oldL]
  have holdLinv_nonneg : 0 ≤ oldLinv := by
    dsimp [oldLinv]
    exact inv_nonneg.mpr
      (Homogenization.multiscale_ellipticity_lambdaSq_finite_nonneg
        Q (s / 2) 2 (publicCoeffField Q a)
        (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 ≤ (s / 2) * (2 : ℝ)))
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.LambdaSq_nonneg (Q := Q) (a := a)
        (q := Ch02.MultiscaleExponent.finite 2) hs_half (by norm_num)) _
  have hL_nonneg : 0 ≤ L := by
    dsimp [L, poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg (Q := Q) (a := a)
        (q := Ch02.MultiscaleExponent.finite 2) hs_half (by norm_num)) _
  have hLinv_nonneg : 0 ≤ Linv := by
    dsimp [Linv]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_nonneg (Q := Q) (a := a)
        (q := Ch02.MultiscaleExponent.finite 2) hs_half (by norm_num)) _
  have hH_nonneg' : 0 ≤ H := by simpa [H] using hH_nonneg
  have hE_nonneg : 0 ≤ E := by simp [E]
  have hB_nonneg' : 0 ≤ B := by simpa [B] using hB_nonneg
  have hMhalf_le : oldMhalf ≤ D * Mhalf := by
    simpa [D, oldMhalf, Mhalf] using
      sqrt_matNorm_le_dim_mul_constantCoeffMatrixNormHalf a0
  have hM_le : oldM ≤ D * M := by
    simpa [D, oldM, M] using
      matNorm_le_dim_mul_constantCoeffMatrixNorm a0
  have hP_le : oldP ≤ D * P := by
    simpa [D, oldP, P] using
      sqrt_LambdaSq_publicCoeffField_finite_two_le_dim_mul_poincareUpperEllipticityFactor
        Q a hs_half
  have hL_le : oldL ≤ D * L := by
    simpa [D, oldL, L] using
      sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
        Q a hs_half
  have hLinv_le : oldLinv ≤ D * Linv := by
    simpa [D, oldLinv, Linv] using
      lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_public_rpow_neg_one
        Q a hs_half
  have hE_eq : E = forcedSolutionEnergyNorm Q a u := by
    simpa [E] using
      (forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
        (Q := Q) (a := a) u).symm
  have hterm_energy :
      s⁻¹ * oldMhalf * H * E ≤
        D ^ 2 * (s⁻¹ * Mhalf * H * E) := by
    calc
      s⁻¹ * oldMhalf * H * E ≤ s⁻¹ * (D * Mhalf) * H * E := by
        gcongr
      _ = D * (s⁻¹ * Mhalf * H * E) := by ring
      _ ≤ D ^ 2 * (s⁻¹ * Mhalf * H * E) := by
        exact mul_le_mul_of_nonneg_right hD_le_sq
          (mul_nonneg (mul_nonneg (mul_nonneg hs_inv_nonneg hMhalf_nonneg)
            hH_nonneg') hE_nonneg)
  have hterm_resp :
      Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H ≤
        D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H) := by
    have hprod : oldMhalf * oldL ≤ (D * Mhalf) * (D * L) :=
      mul_le_mul hMhalf_le hL_le holdL_nonneg
        (mul_nonneg hD_nonneg hMhalf_nonneg)
    calc
      Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H =
          Real.rpow s (-(5 / 2 : ℝ)) * (oldMhalf * oldL) * H := by ring
      _ ≤
          Real.rpow s (-(5 / 2 : ℝ)) * ((D * Mhalf) * (D * L)) * H := by
            gcongr
      _ = D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H) := by ring
  have hterm_weak :
      Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL ≤
        D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * P * L) := by
    have hprod : oldP * oldL ≤ (D * P) * (D * L) :=
      mul_le_mul hP_le hL_le holdL_nonneg (mul_nonneg hD_nonneg hP_nonneg)
    calc
      Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL =
          Real.rpow s (-(5 / 2 : ℝ)) * (oldP * oldL) := by ring
      _ ≤ Real.rpow s (-(5 / 2 : ℝ)) * ((D * P) * (D * L)) := by
            gcongr
      _ = D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * P * L) := by ring
  have hterm_poincare :
      Real.rpow s (-3 : ℝ) * oldM * oldLinv ≤
        D ^ 2 * (Real.rpow s (-3 : ℝ) * M * Linv) := by
    have hprod : oldM * oldLinv ≤ (D * M) * (D * Linv) :=
      mul_le_mul hM_le hLinv_le holdLinv_nonneg
        (mul_nonneg hD_nonneg hM_nonneg)
    calc
      Real.rpow s (-3 : ℝ) * oldM * oldLinv =
          Real.rpow s (-3 : ℝ) * (oldM * oldLinv) := by ring
      _ ≤ Real.rpow s (-3 : ℝ) * ((D * M) * (D * Linv)) := by
            gcongr
      _ = D ^ 2 * (Real.rpow s (-3 : ℝ) * M * Linv) := by ring
  have htail :
      (Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H +
          Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL +
        Real.rpow s (-3 : ℝ) * oldM * oldLinv) * B ≤
        D ^ 2 *
          ((Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H +
              Real.rpow s (-(5 / 2 : ℝ)) * P * L +
            Real.rpow s (-3 : ℝ) * M * Linv) * B) := by
    have hsum :
        Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H +
            Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL +
          Real.rpow s (-3 : ℝ) * oldM * oldLinv ≤
          D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H) +
              D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * P * L) +
            D ^ 2 * (Real.rpow s (-3 : ℝ) * M * Linv) := by
      exact add_le_add (add_le_add hterm_resp hterm_weak) hterm_poincare
    calc
      (Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H +
          Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL +
        Real.rpow s (-3 : ℝ) * oldM * oldLinv) * B ≤
        (D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H) +
              D ^ 2 * (Real.rpow s (-(5 / 2 : ℝ)) * P * L) +
            D ^ 2 * (Real.rpow s (-3 : ℝ) * M * Linv)) * B := by
          exact mul_le_mul_of_nonneg_right hsum hB_nonneg'
      _ =
        D ^ 2 *
          ((Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H +
              Real.rpow s (-(5 / 2 : ℝ)) * P * L +
            Real.rpow s (-3 : ℝ) * M * Linv) * B) := by ring
  have hsum_total :
      s⁻¹ * oldMhalf * H * E +
          (Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H +
              Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL +
            Real.rpow s (-3 : ℝ) * oldM * oldLinv) * B ≤
        D ^ 2 *
          (s⁻¹ * Mhalf * H * E +
            (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H +
                Real.rpow s (-(5 / 2 : ℝ)) * P * L +
              Real.rpow s (-3 : ℝ) * M * Linv) * B) := by
    calc
      s⁻¹ * oldMhalf * H * E +
          (Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H +
              Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL +
            Real.rpow s (-3 : ℝ) * oldM * oldLinv) * B ≤
        D ^ 2 * (s⁻¹ * Mhalf * H * E) +
          D ^ 2 *
            ((Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H +
                Real.rpow s (-(5 / 2 : ℝ)) * P * L +
              Real.rpow s (-3 : ℝ) * M * Linv) * B) :=
          add_le_add hterm_energy htail
      _ =
        D ^ 2 *
          (s⁻¹ * Mhalf * H * E +
            (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H +
                Real.rpow s (-(5 / 2 : ℝ)) * P * L +
              Real.rpow s (-3 : ℝ) * M * Linv) * B) := by ring
  calc
    C * _root_.Homogenization.coarseFluxResponseRHSBound Q (publicCoeffField Q a)
        a0.matrix s (forcedSolutionGradientField u) g =
        C *
          (s⁻¹ * oldMhalf * H * E +
            (Real.rpow s (-(5 / 2 : ℝ)) * oldMhalf * oldL * H +
                Real.rpow s (-(5 / 2 : ℝ)) * oldP * oldL +
              Real.rpow s (-3 : ℝ) * oldM * oldLinv) * B) := by
          unfold _root_.Homogenization.coarseFluxResponseRHSBound
          rw [herror]
    _ ≤
        C *
          (D ^ 2 *
            (s⁻¹ * Mhalf * H * E +
              (Real.rpow s (-(5 / 2 : ℝ)) * Mhalf * L * H +
                  Real.rpow s (-(5 / 2 : ℝ)) * P * L +
                Real.rpow s (-3 : ℝ) * M * Linv) * B)) :=
          mul_le_mul_of_nonneg_left hsum_total hC
    _ =
        coarseFluxResponseWithRHSRHS (((d : ℝ) ^ 2) * C) Q a a0 s g u := by
          unfold coarseFluxResponseWithRHSRHS
          simp [D, Mhalf, M, P, L, Linv, H, E, B, hE_eq,
            scaleNormalizedPositiveBesovVectorSeminormTwo]
          ring

end

end Ch03
end Book
end Homogenization
