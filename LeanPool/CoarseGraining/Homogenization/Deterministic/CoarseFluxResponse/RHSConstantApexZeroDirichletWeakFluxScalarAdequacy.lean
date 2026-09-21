/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletScalarAdequacy

/-! # RHSConstant Apex Zero Dirichlet Weak Flux Scalar Adequacy -/

namespace Homogenization

noncomputable section

/-!
# Weak-flux scalar adequacy for the zero-Dirichlet RHS apex

This leaf continues the weak-flux displayed scalar calculation after the
Poincare scalar adequacy discharge.  It closes the weak-flux energy scale and
composes it with the force-scale coefficient comparison, leaving only the
separate tail allocations.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

private theorem weakFlux_inv_pow_four_le_rpow_neg_five_halves_sq {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (s⁻¹) ^ 4 ≤ (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 := by
  have hs_inv_ge_one : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  have hs_inv_pos : 0 < s⁻¹ := inv_pos.mpr hs
  have hpow :
      Real.rpow (s⁻¹) (4 : ℝ) ≤ Real.rpow (s⁻¹) (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs_inv_ge_one (by norm_num)
  have hpow_nat : (s⁻¹) ^ 4 ≤ Real.rpow (s⁻¹) (5 : ℝ) := by
    simpa using hpow
  have hright :
      (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 =
        Real.rpow (s⁻¹) (5 : ℝ) := by
    change (s ^ (-(5 / 2 : ℝ))) ^ 2 = (s⁻¹) ^ (5 : ℝ)
    rw [Real.rpow_neg_eq_inv_rpow]
    rw [sq]
    rw [← Real.rpow_add hs_inv_pos (5 / 2 : ℝ) (5 / 2 : ℝ)]
    norm_num
  calc
    (s⁻¹) ^ 4 ≤ Real.rpow (s⁻¹) (5 : ℝ) := hpow_nat
    _ = (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 := hright.symm

private theorem weakFlux_inv_pow_five_eq_rpow_neg_five_halves_sq {s : ℝ}
    (hs : 0 < s) :
    (s⁻¹) ^ 5 = (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 := by
  have hs_inv_pos : 0 < s⁻¹ := inv_pos.mpr hs
  have hright :
      (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 =
        Real.rpow (s⁻¹) (5 : ℝ) := by
    change (s ^ (-(5 / 2 : ℝ))) ^ 2 = (s⁻¹) ^ (5 : ℝ)
    rw [Real.rpow_neg_eq_inv_rpow]
    rw [sq]
    rw [← Real.rpow_add hs_inv_pos (5 / 2 : ℝ) (5 / 2 : ℝ)]
    norm_num
  have hpow_five : Real.rpow (s⁻¹) (5 : ℝ) = (s⁻¹) ^ 5 := by
    simp
  exact hpow_five.symm.trans hright.symm

/-- Corrected weak-flux force-scale adequacy with manuscript `Lambda * lambda^{-1}` units. -/
theorem zeroTraceDirichletWeakFluxDisplayedForceScale_le_compact_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    {AweakForce : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hAweakForce :
      2500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        AweakForce) :
    2500 * (s⁻¹) ^ 4 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
      AweakForce *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let Lam : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  have hN_sq_nonneg : 0 ≤ N ^ 2 := sq_nonneg N
  have hLam_nonneg : 0 ≤ Lam := by
    dsimp [Lam]
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hcompact_nonneg : 0 ≤ Lam * L := mul_nonneg hLam_nonneg hL_nonneg
  have hscale := weakFlux_inv_pow_four_le_rpow_neg_five_halves_sq hs hs_le
  have hscale_scaled :=
    mul_le_mul_of_nonneg_left hscale
      (mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (2500 : ℝ)) hN_sq_nonneg)
        hcompact_nonneg)
  have htarget_nonneg :
      0 ≤ (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * Lam * L := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) hLam_nonneg)
      hL_nonneg
  have hforce_scaled :=
    mul_le_mul_of_nonneg_right hAweakForce htarget_nonneg
  calc
    2500 * (s⁻¹) ^ 4 * LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2
        =
      (2500 * N ^ 2 * (Lam * L)) * (s⁻¹) ^ 4 := by
        dsimp [N, Lam, L]
        ring
    _ ≤ (2500 * N ^ 2 * (Lam * L)) *
          (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 := hscale_scaled
    _ = (2500 * N ^ 2) *
          ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * Lam * L) := by ring
    _ ≤ AweakForce *
          ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * Lam * L) := by
        simpa [N, Lam, L, mul_assoc, mul_left_comm, mul_comm] using
          hforce_scaled
    _ =
      AweakForce *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
        dsimp [Lam, L]

/-- Weak-flux energy component adequacy after expanding the zero-Dirichlet envelope. -/
theorem zeroTraceDirichletWeakFluxDisplayedEnergyScale_le_compact_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g) :
    50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        zeroTraceDirichletEnergyEnvelope Q a s g ≤
      (32500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let Lam : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  have hLam_nonneg : 0 ≤ Lam := by
    dsimp [Lam]
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hcoeff_nonneg : 0 ≤ 50 * (s⁻¹) ^ 2 * Lam := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (50 : ℝ)) (sq_nonneg (s⁻¹)))
        hLam_nonneg
  have henv :=
    zeroTraceDirichletEnergyEnvelope_le_poincareDisplayedScale_noteConstants
      Q a g hs hG_nonneg
  have hmul := mul_le_mul_of_nonneg_left henv hcoeff_nonneg
  have hscale := weakFlux_inv_pow_four_le_rpow_neg_five_halves_sq hs hs_le
  have hfactor_nonneg : 0 ≤ 32500 * N ^ 2 * Lam * L * G ^ 2 := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : 0 ≤ (32500 : ℝ)) (sq_nonneg N))
            hLam_nonneg)
          hL_nonneg)
        (sq_nonneg G)
  have hscaled := mul_le_mul_of_nonneg_left hscale hfactor_nonneg
  calc
    50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        zeroTraceDirichletEnergyEnvelope Q a s g
        ≤ 50 * (s⁻¹) ^ 2 * Lam *
          (650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) := by
        simpa [Lam, L, N, G, mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = 32500 * N ^ 2 * Lam * L * G ^ 2 * (s⁻¹) ^ 4 := by ring
    _ ≤ 32500 * N ^ 2 * Lam * L * G ^ 2 *
          (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 := hscaled
    _ =
      (32500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
        dsimp [N, Lam, L, G]
        ring

/--
Zero-trace gradient-tail adequacy at the raw scale produced by the
zero-Dirichlet energy envelope.

This is the complete tail algebra before the final coefficient conversion from
`lambda^{-2}` to the manuscript `Lambda * lambda^{-1}` scale.
-/
theorem zeroTraceDirichletGradientTailBudget_mul_five_inv_le_raw_lambdaInv_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d)
    (hs : 0 < s)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g) :
    (5 * s⁻¹) * zeroTraceDirichletGradientTailBudget Q a s g ≤
      (887500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
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
  have htail_coeff_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 * L := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        hL_nonneg
  have henergy :=
    zeroTraceDirichletEnergyEnvelope_le_poincareDisplayedScale_noteConstants
      Q a g hs hG_nonneg
  have henergy_scaled :=
    mul_le_mul_of_nonneg_left henergy htail_coeff_nonneg
  have htail_base :
      zeroTraceDirichletGradientTailBudget Q a s g ≤
        177500 * (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2 := by
    have henergy_term :
        250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g ≤
          250 * (s⁻¹) ^ 2 * L *
            (650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) := by
      simpa [L, N, G, mul_assoc, mul_left_comm, mul_comm] using
        henergy_scaled
    have hforce_term :
        15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 =
          15000 * (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2 := by
      dsimp [L, N, G]
    unfold zeroTraceDirichletGradientTailBudget
    calc
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            zeroTraceDirichletEnergyEnvelope Q a s g +
          15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2
          ≤
        250 * (s⁻¹) ^ 2 * L *
            (650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) +
          15000 * (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2 :=
          add_le_add henergy_term hforce_term.le
      _ = 177500 * (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2 := by ring
  have htail_mul :=
    mul_le_mul_of_nonneg_left htail_base (by positivity : 0 ≤ 5 * s⁻¹)
  calc
    (5 * s⁻¹) * zeroTraceDirichletGradientTailBudget Q a s g
        ≤ (5 * s⁻¹) *
          (177500 * (s⁻¹) ^ 4 * L ^ 2 * N ^ 2 * G ^ 2) := htail_mul
    _ = 887500 * N ^ 2 * ((s⁻¹) ^ 5 * L ^ 2 * G ^ 2) := by ring
    _ =
        887500 * N ^ 2 *
          ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * L ^ 2 * G ^ 2) := by
        rw [weakFlux_inv_pow_five_eq_rpow_neg_five_halves_sq hs]
    _ =
        (887500 * N ^ 2) *
          ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * L ^ 2 * G ^ 2) := by
        ring
    _ =
      (887500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
        dsimp [N, L, G]

/--
Weak-flux `BV` tail adequacy for the tight averaged-budget choice.  This is
the algebraic allocation used when the harmonic-remainder BV constant is chosen
as the sum of the three averaged budget pieces.
-/
theorem zeroTraceDirichletWeakFluxDisplayedBVTailScale_le_compact_sq_of_averaged_budget_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g : Vec d → Vec d)
    {Brho BomegaNeg BomegaForce Arho AomegaNeg AomegaForce : ℝ}
    (hs : 0 < s)
    (hBrho :
      Brho ≤
        Arho *
          ((s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) a *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    (hBomegaNeg :
      BomegaNeg ≤
        AomegaNeg *
          ((s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) a *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    (hBomegaForce :
      BomegaForce ≤
        AomegaForce *
          ((s⁻¹) ^ 4 *
            LambdaSq Q (s / 2) (.finite 2) a *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) :
    (5 * s⁻¹) * (Brho + (BomegaNeg + BomegaForce)) ≤
      (5 * (Arho + (AomegaNeg + AomegaForce))) *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let Lam : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let K4 : ℝ := (s⁻¹) ^ 4 * Lam * L * G ^ 2
  let K5 : ℝ := (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * Lam * L * G ^ 2
  have hsum :
      Brho + (BomegaNeg + BomegaForce) ≤
        (Arho + (AomegaNeg + AomegaForce)) * K4 := by
    calc
      Brho + (BomegaNeg + BomegaForce)
          ≤ Arho * K4 + (AomegaNeg * K4 + AomegaForce * K4) := by
            exact add_le_add
              (by simpa [K4, Lam, L, G] using hBrho)
              (add_le_add
                (by simpa [K4, Lam, L, G] using hBomegaNeg)
                (by simpa [K4, Lam, L, G] using hBomegaForce))
      _ = (Arho + (AomegaNeg + AomegaForce)) * K4 := by ring
  have htail_coeff_nonneg : 0 ≤ 5 * s⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum htail_coeff_nonneg
  calc
    (5 * s⁻¹) * (Brho + (BomegaNeg + BomegaForce))
        ≤ (5 * s⁻¹) *
          ((Arho + (AomegaNeg + AomegaForce)) * K4) := hscaled
    _ =
      (5 * (Arho + (AomegaNeg + AomegaForce))) *
        ((s⁻¹) ^ 5 * Lam * L * G ^ 2) := by
        dsimp [K4]
        ring
    _ =
      (5 * (Arho + (AomegaNeg + AomegaForce))) * K5 := by
        dsimp [K5]
        rw [weakFlux_inv_pow_five_eq_rpow_neg_five_halves_sq hs]
        simp only [Real.rpow_eq_pow]
    _ =
      (5 * (Arho + (AomegaNeg + AomegaForce))) *
        ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
        dsimp [K5, Lam, L, G]

end ZeroTraceDirichletCorrectorData

end

end Homogenization
