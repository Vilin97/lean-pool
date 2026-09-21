/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletEstimates

/-! # RHSConstant Apex Zero Dirichlet Scalar Adequacy -/

namespace Homogenization

noncomputable section

/-!
# Scalar adequacy for the zero-Dirichlet RHS flux-response apex

This leaf records the Poincare displayed scalar comparison in the form used by
the manuscript constant absorption.  The weak-flux displayed comparison now
lives in `RHSConstantApexZeroDirichletWeakFluxScalarAdequacy`, where the
manuscript `Lambda * lambda^{-1}` force units are used directly.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

private theorem inv_pow_four_le_rpow_neg_three_sq {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (s⁻¹) ^ 4 ≤ (Real.rpow s (-3 : ℝ)) ^ 2 := by
  have hs_inv_ge_one : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  have hpow :
      Real.rpow (s⁻¹) (4 : ℝ) ≤ Real.rpow (s⁻¹) (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs_inv_ge_one (by norm_num)
  have hpow_nat : (s⁻¹) ^ 4 ≤ (s⁻¹) ^ 6 := by
    simpa using hpow
  have hright :
      (Real.rpow s (-3 : ℝ)) ^ 2 = (s⁻¹) ^ 6 := by
    have hneg :
        Real.rpow s (-3 : ℝ) = Real.rpow (s⁻¹) (3 : ℝ) := by
      simp
    have hpow_three : Real.rpow (s⁻¹) (3 : ℝ) = (s⁻¹) ^ 3 := by
      simp
    rw [hneg, hpow_three]
    ring
  calc
    (s⁻¹) ^ 4 ≤ (s⁻¹) ^ 6 := hpow_nat
    _ = (Real.rpow s (-3 : ℝ)) ^ 2 := hright.symm

/--
Positivity of the compact Poincare correction-square base in the nondegenerate
case.
-/
theorem zeroTraceDirichletPoincareDisplayedScalarAdequacyBase_pos
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d)
    (hs : 0 < s)
    (hmat_pos : 0 < matNorm a0)
    (hlambda_pos : 0 < lambdaSq Q (s / 2) (.finite 2) a)
    (hG_pos : 0 < cubeBesovPositiveVectorSeminormTwo Q s g) :
    0 <
      (Real.rpow s (-3 : ℝ)) ^ 2 *
        (matNorm a0) ^ 2 *
        ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hs_pow_pos :
      0 < (Real.rpow s (-3 : ℝ)) ^ 2 :=
    pow_pos (Real.rpow_pos_of_pos hs _) 2
  have hmat_sq_pos : 0 < (matNorm a0) ^ 2 :=
    pow_pos hmat_pos 2
  have hlambda_inv_sq_pos :
      0 < ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 :=
    pow_pos (inv_pos.mpr hlambda_pos) 2
  have hG_sq_pos :
      0 < (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
    pow_pos hG_pos 2
  exact mul_pos (mul_pos (mul_pos hs_pow_pos hmat_sq_pos)
    hlambda_inv_sq_pos) hG_sq_pos

/-- Sharp zero-Dirichlet energy envelope control after expanding the square-root force term. -/
theorem zeroTraceDirichletEnergyEnvelope_le_poincareDisplayedScale_noteConstants
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d)
    (hs : 0 < s)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g) :
    zeroTraceDirichletEnergyEnvelope Q a s g ≤
      650 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let M : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let X : ℝ :=
    15000 * (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hsqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_two_ge_one : 1 ≤ Real.sqrt 2 := by
    exact Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        hsqrt_two_nonneg)
  have hM_le_N : M ≤ N := by
    dsimp [M, N]
    calc
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
          = ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) * 1 := by ring
      _ ≤ ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left hsqrt_two_ge_one
            (mul_nonneg (by exact_mod_cast Nat.zero_le d)
              (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      _ = (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2) := by ring
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hG : 0 ≤ G := by
    dsimp [G]
    exact hG_nonneg
  have hs_inv_four_nonneg : 0 ≤ (s⁻¹) ^ 4 := by
    rw [show (s⁻¹) ^ 4 = ((s⁻¹) ^ 2) ^ 2 by ring]
    exact sq_nonneg _
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hs_inv_sq_nonneg : 0 ≤ (s⁻¹) ^ 2 := sq_nonneg _
  have hsqrt_bound :
      Real.sqrt X ≤ 200 * (s⁻¹) ^ 2 * L * N * G := by
    have hrhs_nonneg :
        0 ≤ 200 * (s⁻¹) ^ 2 * L * N * G := by
      exact
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num : 0 ≤ (200 : ℝ))
                hs_inv_sq_nonneg)
              hL_nonneg)
            hN_nonneg)
          hG
    refine Real.sqrt_le_of_le_sq hX_nonneg hrhs_nonneg ?_
    have hfactor_nonneg :
        0 ≤ (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2 := by
      exact
        mul_nonneg
          (mul_nonneg (mul_nonneg hs_inv_four_nonneg (sq_nonneg L))
            (sq_nonneg N))
          (sq_nonneg G)
    calc
      X = 15000 * ((s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2) := by
            dsimp [X]
            ring
      _ ≤ 40000 * ((s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2) := by
            nlinarith
      _ = (200 * (s⁻¹) ^ 2 * L * N * G) ^ 2 := by ring
  have hMG_nonneg : 0 ≤ M * G := mul_nonneg hM_nonneg hG
  have hNG_nonneg : 0 ≤ N * G := mul_nonneg hN_nonneg hG
  have hMG_le_NG : M * G ≤ N * G :=
    mul_le_mul_of_nonneg_right hM_le_N hG
  have hMG_sq_le_NG_sq : (M * G) ^ 2 ≤ (N * G) ^ 2 := by
    nlinarith [hMG_nonneg, hNG_nonneg, hMG_le_NG]
  have henergy_coeff_nonneg : 0 ≤ 250 * (s⁻¹) ^ 2 * L := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) hs_inv_sq_nonneg)
        hL_nonneg
  have hfirst :
      (M * G) ^ 2 * (250 * (s⁻¹) ^ 2 * L) ≤
        250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right
      hMG_sq_le_NG_sq henergy_coeff_nonneg
    calc
      (M * G) ^ 2 * (250 * (s⁻¹) ^ 2 * L)
          ≤ (N * G) ^ 2 * (250 * (s⁻¹) ^ 2 * L) := hscaled
      _ = 250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by ring
  have habs_MG_le_NG : |M * G| ≤ N * G := by
    rw [abs_of_nonneg hMG_nonneg]
    exact hMG_le_NG
  have hsqrt_rhs_nonneg :
      0 ≤ 200 * (s⁻¹) ^ 2 * L * N * G := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : 0 ≤ (200 : ℝ))
              hs_inv_sq_nonneg)
            hL_nonneg)
          hN_nonneg)
        hG
  have hsecond :
      2 * |M * G| * Real.sqrt X ≤
        400 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    have hmul := mul_le_mul habs_MG_le_NG hsqrt_bound
      (Real.sqrt_nonneg X) hNG_nonneg
    nlinarith
  have henv_eq :
      zeroTraceDirichletEnergyEnvelope Q a s g =
        (M * G) ^ 2 * (250 * (s⁻¹) ^ 2 * L) +
          2 * |M * G| * Real.sqrt X := by
    unfold zeroTraceDirichletEnergyEnvelope
    dsimp [G, L, M, N, X]
    ring_nf
  calc
    zeroTraceDirichletEnergyEnvelope Q a s g =
        (M * G) ^ 2 * (250 * (s⁻¹) ^ 2 * L) +
          2 * |M * G| * Real.sqrt X := henv_eq
    _ ≤
        250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 +
          400 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 :=
        add_le_add hfirst hsecond
    _ ≤ 650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
        ring_nf
        rfl
    _ =
      650 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
        dsimp [G, L, N]

/-- Poincare energy component adequacy after expanding the zero-Dirichlet envelope. -/
theorem zeroTraceDirichletPoincareDisplayedEnergyScale_le_compact_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g) :
    250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        zeroTraceDirichletEnergyEnvelope Q a s g ≤
      (162500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        ((Real.rpow s (-3 : ℝ)) ^ 2 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (Real.sqrt_nonneg 2))
  have hG : 0 ≤ G := by
    dsimp [G]
    exact hG_nonneg
  have hs_inv_sq_nonneg : 0 ≤ (s⁻¹) ^ 2 := sq_nonneg _
  have hcoeff_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 * L := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) hs_inv_sq_nonneg)
        hL_nonneg
  have henv :=
    zeroTraceDirichletEnergyEnvelope_le_poincareDisplayedScale_noteConstants
      Q a g hs hG_nonneg
  have hmul := mul_le_mul_of_nonneg_left henv hcoeff_nonneg
  have hs_inv_four_le := inv_pow_four_le_rpow_neg_three_sq hs hs_le
  have hfactor_nonneg :
      0 ≤ 162500 * N ^ 2 * L ^ 2 * G ^ 2 := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (162500 : ℝ))
            (sq_nonneg N))
          (sq_nonneg L))
        (sq_nonneg G)
  have hscale :=
    mul_le_mul_of_nonneg_left hs_inv_four_le hfactor_nonneg
  calc
    250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        zeroTraceDirichletEnergyEnvelope Q a s g
        ≤
      250 * (s⁻¹) ^ 2 * L *
        (650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) := by
        simpa [L, N, G, mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = 162500 * N ^ 2 * L ^ 2 * G ^ 2 * (s⁻¹) ^ 4 := by ring
    _ ≤ 162500 * N ^ 2 * L ^ 2 * G ^ 2 *
          (Real.rpow s (-3 : ℝ)) ^ 2 := hscale
    _ =
      (162500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        ((Real.rpow s (-3 : ℝ)) ^ 2 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
        dsimp [N, L, G]
        ring

/-- Poincare force component adequacy: the `s^{-4}` term is absorbed by the compact `s^{-6}` scale. -/
theorem zeroTraceDirichletPoincareDisplayedForceScale_le_compact_sq
    {d : ℕ} {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    15000 * (s⁻¹) ^ 4 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
      (15000 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        (Real.rpow s (-3 : ℝ)) ^ 2 := by
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  have hfactor_nonneg : 0 ≤ 15000 * N ^ 2 := by
    exact mul_nonneg (by norm_num : 0 ≤ (15000 : ℝ)) (sq_nonneg N)
  have hscale := inv_pow_four_le_rpow_neg_three_sq hs hs_le
  have hscaled := mul_le_mul_of_nonneg_left hscale hfactor_nonneg
  calc
    15000 * (s⁻¹) ^ 4 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2
        =
      15000 * N ^ 2 * (s⁻¹) ^ 4 := by
        dsimp [N]
        ring
    _ ≤ 15000 * N ^ 2 * (Real.rpow s (-3 : ℝ)) ^ 2 := hscaled
    _ =
      (15000 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        (Real.rpow s (-3 : ℝ)) ^ 2 := by
        dsimp [N]

/-- Poincare scalar adequacy from the energy-envelope and force-scale estimates. -/
theorem zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_energyEnvelope_and_force_scale_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d)
    {APoincareEnergy APoincareForce : ℝ}
    (hPoincareEnergy :
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g ≤
        APoincareEnergy *
          ((Real.rpow s (-3 : ℝ)) ^ 2 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    (hPoincareForceScale :
      15000 * (s⁻¹) ^ 4 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        APoincareForce * (Real.rpow s (-3 : ℝ)) ^ 2)
    (halloc : APoincareEnergy + APoincareForce ≤ C ^ 2) :
    zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let K : ℝ :=
    (Real.rpow s (-3 : ℝ)) ^ 2 *
      (matNorm a0) ^ 2 *
      L ^ 2 *
      G ^ 2
  have hmat_sq_nonneg : 0 ≤ (matNorm a0) ^ 2 := sq_nonneg _
  have htail_factor_nonneg : 0 ≤ (matNorm a0) ^ 2 * L ^ 2 * G ^ 2 := by
    exact
      mul_nonneg (mul_nonneg hmat_sq_nonneg (sq_nonneg L))
        (sq_nonneg G)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg (Real.rpow s (-3 : ℝ)))
            hmat_sq_nonneg)
          (sq_nonneg L))
        (sq_nonneg G)
  have henergy_mul :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g) ≤
        APoincareEnergy * K := by
    have hscaled := mul_le_mul_of_nonneg_left hPoincareEnergy hmat_sq_nonneg
    calc
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g)
          ≤
        (matNorm a0) ^ 2 *
          (APoincareEnergy *
            ((Real.rpow s (-3 : ℝ)) ^ 2 *
              ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := hscaled
      _ = APoincareEnergy * K := by
        dsimp [K, L, G]
        ring
  have hforce_mul :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        APoincareForce * K := by
    have hscaled :=
      mul_le_mul_of_nonneg_right hPoincareForceScale htail_factor_nonneg
    calc
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
          =
        (15000 * (s⁻¹) ^ 4 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
          ((matNorm a0) ^ 2 * L ^ 2 * G ^ 2) := by
        dsimp [L, G]
        ring
      _ ≤
        (APoincareForce * (Real.rpow s (-3 : ℝ)) ^ 2) *
          ((matNorm a0) ^ 2 * L ^ 2 * G ^ 2) := hscaled
      _ = APoincareForce * K := by
        dsimp [K]
        ring
  have halloc_scaled :
      APoincareEnergy * K + APoincareForce * K ≤ C ^ 2 * K := by
    have hscaled := mul_le_mul_of_nonneg_right halloc hK_nonneg
    calc
      APoincareEnergy * K + APoincareForce * K =
          (APoincareEnergy + APoincareForce) * K := by ring
      _ ≤ C ^ 2 * K := hscaled
  have hbudget_le :
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
        APoincareEnergy * K + APoincareForce * K := by
    unfold zeroTraceDirichletPoincareDisplayedScalarBudget
    nlinarith
  have htarget :
      C ^ 2 * K =
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
    calc
      C ^ 2 * K =
          C ^ 2 *
            (Real.rpow s (-3 : ℝ)) ^ 2 *
            (matNorm a0) ^ 2 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
            dsimp [K, L, G]
            ring
      _ = (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 :=
          (const_mul_coarseFluxResponseRHSPoincareCorrectionBound_sq_eq
            Q a a0 C s g).symm
  calc
    zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g
        ≤ APoincareEnergy * K + APoincareForce * K := hbudget_le
    _ ≤ C ^ 2 * K := halloc_scaled
    _ = (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 :=
      htarget

/-- Poincare component target from the energy-envelope and force-scale estimates. -/
theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_energyEnvelope_and_force_scale_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d)
    {APoincareEnergy APoincareForce : ℝ}
    (hPoincareEnergy :
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          zeroTraceDirichletEnergyEnvelope Q a s g ≤
        APoincareEnergy *
          ((Real.rpow s (-3 : ℝ)) ^ 2 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    (hPoincareForceScale :
      15000 * (s⁻¹) ^ 4 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        APoincareForce * (Real.rpow s (-3 : ℝ)) ^ 2)
    (halloc : APoincareEnergy + APoincareForce ≤ C ^ 2) :
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g :=
  zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_displayed_bound
    Q a a0 C s g
    (zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_energyEnvelope_and_force_scale_bounds
      Q a a0 C s g hPoincareEnergy hPoincareForceScale halloc)

/-- Poincare scalar adequacy with the analytic estimates discharged into one constant bound. -/
theorem zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_const_ge
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C : ℝ) {s : ℝ} (g : Vec d → Vec d)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (hC_sq :
      177500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        C ^ 2) :
    zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  refine
    zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_energyEnvelope_and_force_scale_bounds
      (Q := Q) (a := a) (a0 := a0) (C := C) (s := s) (g := g)
      (APoincareEnergy :=
        162500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2)
      (APoincareForce :=
        15000 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2)
      ?_ ?_ ?_
  · exact zeroTraceDirichletPoincareDisplayedEnergyScale_le_compact_sq
      Q a g hs hs_le hG_nonneg
  · exact zeroTraceDirichletPoincareDisplayedForceScale_le_compact_sq
      hs hs_le
  · nlinarith

/-- Poincare component target with scalar adequacy discharged into one constant bound. -/
theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_const_ge
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C : ℝ) {s : ℝ} (g : Vec d → Vec d)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (hC_sq :
      177500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        C ^ 2) :
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g :=
  zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_displayed_bound
    Q a a0 C s g
    (zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_const_ge
      Q a a0 C g hs hs_le hG_nonneg hC_sq)

/--
Poincare displayed scalar adequacy in normalized `C^2` form.
-/
theorem zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_div_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d)
    (hbase_pos :
      0 <
        (Real.rpow s (-3 : ℝ)) ^ 2 *
          (matNorm a0) ^ 2 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
    (hC_sq :
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g /
          ((Real.rpow s (-3 : ℝ)) ^ 2 *
            (matNorm a0) ^ 2 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        C ^ 2) :
    zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  let K : ℝ :=
    (Real.rpow s (-3 : ℝ)) ^ 2 *
      (matNorm a0) ^ 2 *
      ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2
  have hbudget_le_grouped :
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
        C ^ 2 * K := by
    exact (div_le_iff₀ (by simpa [K] using hbase_pos)).mp
      (by simpa [K] using hC_sq)
  have hbudget_le_expanded :
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g ≤
        C ^ 2 *
          (Real.rpow s (-3 : ℝ)) ^ 2 *
          (matNorm a0) ^ 2 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    calc
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g
          ≤ C ^ 2 * K := hbudget_le_grouped
      _ =
          C ^ 2 *
            (Real.rpow s (-3 : ℝ)) ^ 2 *
            (matNorm a0) ^ 2 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
            dsimp [K]
            ring
  simpa [const_mul_coarseFluxResponseRHSPoincareCorrectionBound_sq_eq Q a a0 C s g]
    using hbudget_le_expanded

/--
The Poincare displayed component target follows from the normalized scalar
adequacy inequality.
-/
theorem zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_div_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (C s : ℝ) (g : Vec d → Vec d)
    (hbase_pos :
      0 <
        (Real.rpow s (-3 : ℝ)) ^ 2 *
          (matNorm a0) ^ 2 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
    (hC_sq :
      zeroTraceDirichletPoincareDisplayedScalarBudget Q a a0 s g /
          ((Real.rpow s (-3 : ℝ)) ^ 2 *
            (matNorm a0) ^ 2 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        C ^ 2) :
    zeroTraceDirichletPoincareDisplayedComponentBoundsClose Q a a0 C s g :=
  zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_displayed_bound
    Q a a0 C s g
    (zeroTraceDirichletPoincareDisplayedScalarBudget_le_const_mul_correctionBound_sq_of_div_le_sq
      Q a a0 C s g hbase_pos hC_sq)

end ZeroTraceDirichletCorrectorData

end

end Homogenization
