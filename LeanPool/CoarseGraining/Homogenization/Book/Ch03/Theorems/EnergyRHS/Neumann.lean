/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.Corrector

/-! # Neumann -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Neumann estimate
-/

noncomputable section

open scoped ENNReal

/-- Public Neumann forced solutions supply the deterministic mean-zero
corrector-energy estimate on the half-open cube. -/
theorem neumannForcedSolutionEnergyAverage_le_force_scale_noteConstants_expanded_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d}
    (w : NeumannForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => w.toH1MeanZero.toH1Function.grad x)) ≤
      500 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let ω := neumannForcedSolutionMeanZeroCorrectorData_publicCoeffField w
  have hdet :=
    ω.coefficientEnergy_average_le_force_scale_noteConstants_expanded
      (s := s) (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      hs hs_lt.le (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      hg.memLp hg.partialSeminorms_bddAbove
  simpa [ω] using hdet

/-- Square-root form of the public Neumann forced-solution energy envelope
before the final dimension-only constant absorption. -/
theorem neumannForcedSolutionEnergyNorm_le_sqrt_force_scale_noteConstants_expanded_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d}
    (w : NeumannForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    neumannForcedSolutionEnergyNorm Q a w ≤
      Real.sqrt
        (500 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  rw [neumannForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    (Q := Q) (a := a) w]
  exact Real.sqrt_le_sqrt
    (neumannForcedSolutionEnergyAverage_le_force_scale_noteConstants_expanded_publicCoeffField
      (Q := Q) (a := a) (s := s) (g := g) w hs hs_lt hg)

/-- Public Neumann forced-solution energy estimate, assuming the displayed
constant dominates the dimension-only scalar from the deterministic envelope. -/
theorem neumannForcedSolutionEnergyNorm_le_publicRHS_of_constant
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_neumann :
      Real.sqrt 500 *
          ((d : ℝ) *
            (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d}
    (w : NeumannForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    neumannForcedSolutionEnergyNorm Q a w ≤
      neumannEnergyWithRHSRHS ((d : ℝ) * C) Q a s g := by
  let L : ℝ := lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a)
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let D : ℝ :=
    (d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2)
  have hs_le : s ≤ 1 := hs_lt.le
  have hs_half : 0 < s / 2 := by nlinarith
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using
      multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
        (publicCoeffField Q a) (by norm_num)
        (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_inv_nonneg : 0 ≤ L⁻¹ := inv_nonneg.mpr hL_nonneg
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hB_nonneg : 0 ≤ B := by
    simpa [B, scaleNormalizedPositiveBesovVectorSeminormTwo] using
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := g) hg
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hD_le :
      D ≤
        (d : ℝ) *
          (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2) := by
    dsimp [D]
    have hpow :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith)
    have hinner :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2 ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg 2)
    exact mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.zero_le d)
  have hs_inv_le :
      s⁻¹ ≤ Real.rpow s (-(3 / 2 : ℝ)) := by
    calc
      s⁻¹ = Real.rpow s (-1 : ℝ) := (Real.rpow_neg_one s).symm
      _ ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hs hs_le (by norm_num)
  have hsqrt_prod :
      Real.sqrt (500 * (s⁻¹) ^ 2 * L⁻¹ * D ^ 2 * B ^ 2) =
        Real.sqrt 500 * s⁻¹ * Real.sqrt (L⁻¹) * D * B := by
    calc
      Real.sqrt (500 * (s⁻¹) ^ 2 * L⁻¹ * D ^ 2 * B ^ 2)
          =
        Real.sqrt (500 * ((s⁻¹) ^ 2 * (L⁻¹ * (D ^ 2 * B ^ 2)))) := by
          ring_nf
      _ =
        Real.sqrt 500 *
          Real.sqrt ((s⁻¹) ^ 2 * (L⁻¹ * (D ^ 2 * B ^ 2))) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 500)]
      _ =
        Real.sqrt 500 *
          (Real.sqrt ((s⁻¹) ^ 2) *
            Real.sqrt (L⁻¹ * (D ^ 2 * B ^ 2))) := by
          rw [Real.sqrt_mul (sq_nonneg s⁻¹)]
      _ =
        Real.sqrt 500 *
          (s⁻¹ * (Real.sqrt (L⁻¹) * Real.sqrt (D ^ 2 * B ^ 2))) := by
          rw [Real.sqrt_sq hs_inv_nonneg, Real.sqrt_mul hL_inv_nonneg]
      _ =
        Real.sqrt 500 * (s⁻¹ * (Real.sqrt (L⁻¹) * (D * B))) := by
          rw [show D ^ 2 * B ^ 2 = (D * B) ^ 2 by ring]
          rw [Real.sqrt_sq (mul_nonneg hD_nonneg hB_nonneg)]
      _ = Real.sqrt 500 * s⁻¹ * Real.sqrt (L⁻¹) * D * B := by ring
  have hconstD :
      Real.sqrt 500 * D ≤ C := by
    calc
      Real.sqrt 500 * D ≤
          Real.sqrt 500 *
            ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) :=
            mul_le_mul_of_nonneg_left hD_le (Real.sqrt_nonneg 500)
      _ ≤ C := hC_neumann
  have hcoeff :
      (Real.sqrt 500 * D) * s⁻¹ ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) := by
    exact mul_le_mul hconstD hs_inv_le hs_inv_nonneg hC_nonneg
  have htail : 0 ≤ Real.sqrt (L⁻¹) * B :=
    mul_nonneg (Real.sqrt_nonneg _) hB_nonneg
  have hsqrtL_public :
      Real.sqrt (L⁻¹) ≤
        (d : ℝ) *
          poincareLowerEllipticityFactor Q a (s / 2)
            (Ch02.MultiscaleExponent.finite 2) := by
    simpa [L] using
      sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
        Q a hs_half
  have hpublic_tail :
      Real.sqrt (L⁻¹) * B ≤
        ((d : ℝ) *
          poincareLowerEllipticityFactor Q a (s / 2)
            (Ch02.MultiscaleExponent.finite 2)) * B :=
    mul_le_mul_of_nonneg_right hsqrtL_public hB_nonneg
  have hcoeff_public_nonneg : 0 ≤ C * Real.rpow s (-(3 / 2 : ℝ)) :=
    mul_nonneg hC_nonneg (Real.rpow_nonneg hs.le _)
  calc
    neumannForcedSolutionEnergyNorm Q a w
        ≤
      Real.sqrt
        (500 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a))⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) :=
        neumannForcedSolutionEnergyNorm_le_sqrt_force_scale_noteConstants_expanded_publicCoeffField
          (Q := Q) (a := a) (s := s) (g := g) w hs hs_lt hg
    _ =
      Real.sqrt 500 * s⁻¹ * Real.sqrt (L⁻¹) * D * B := by
        simpa [L, B, D] using hsqrt_prod
    _ =
      (Real.sqrt 500 * D) * s⁻¹ * (Real.sqrt (L⁻¹) * B) := by ring
    _ ≤
      (C * Real.rpow s (-(3 / 2 : ℝ))) *
        (Real.sqrt (L⁻¹) * B) :=
        mul_le_mul_of_nonneg_right hcoeff htail
    _ ≤
      (C * Real.rpow s (-(3 / 2 : ℝ))) *
        (((d : ℝ) *
          poincareLowerEllipticityFactor Q a (s / 2)
            (Ch02.MultiscaleExponent.finite 2)) * B) :=
        mul_le_mul_of_nonneg_left hpublic_tail hcoeff_public_nonneg
    _ =
      neumannEnergyWithRHSRHS ((d : ℝ) * C) Q a s g := by
        unfold neumannEnergyWithRHSRHS
        simp [B, scaleNormalizedPositiveBesovVectorSeminormTwo]
        ring

end

end Ch03
end Book
end Homogenization
