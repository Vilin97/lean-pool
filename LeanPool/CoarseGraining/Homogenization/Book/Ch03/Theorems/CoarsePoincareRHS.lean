/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.ZeroDirichletEnergy
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge

/-! # Coarse Poincare RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.2.1: Coarse-grained Poincare inequality with right-hand side

This file assembles the public theorem package for
`p.coarse.grained.Poincare.RHS.deterministic.theory` and the auxiliary
zero-Dirichlet energy estimate
`l.zero.Dirichlet.energy.RHS.deterministic.theory`.

## Audit tag

Claim: assemble the public coarse Poincare-with-RHS package and the
zero-Dirichlet energy RHS estimate from the deterministic RHS endpoints.

Downstream target: `InhomogeneousEquationsTheory`.  This file should remain
the single public `CoarsePoincareRHSTheory` endpoint for Section 3.2.1.
-/

noncomputable section

private theorem inv_le_rpow_neg_three_halves {s : ℝ} (hs : 0 < s)
    (hs_le_one : s ≤ 1) :
    s⁻¹ ≤ Real.rpow s (-(3 / 2 : ℝ)) := by
  calc
    s⁻¹ = Real.rpow s (-1 : ℝ) := (Real.rpow_neg_one s).symm
    _ ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hs hs_le_one (by norm_num)

private theorem rpow_three_nat_add_le_nat_add_one (d : ℕ) {s : ℝ}
    (hs_le_one : s ≤ 1) :
    Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
      Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith)

private theorem sqrt_const_mul_fourth_mul_sq_mul_sq_mul_sq
    {A x y z w : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    Real.sqrt (A * x ^ 4 * y ^ 2 * z ^ 2 * w ^ 2) =
      Real.sqrt A * x ^ 2 * y * z * w := by
  have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  calc
    Real.sqrt (A * x ^ 4 * y ^ 2 * z ^ 2 * w ^ 2)
        =
      Real.sqrt (A * (x ^ 4 * (y ^ 2 * (z ^ 2 * w ^ 2)))) := by
        ring_nf
    _ =
      Real.sqrt A * Real.sqrt (x ^ 4 * (y ^ 2 * (z ^ 2 * w ^ 2))) := by
        rw [Real.sqrt_mul hA]
    _ =
      Real.sqrt A * (Real.sqrt (x ^ 4) * Real.sqrt (y ^ 2 * (z ^ 2 * w ^ 2))) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ x ^ 4)]
    _ =
      Real.sqrt A * (x ^ 2 * (y * (z * w))) := by
        rw [show x ^ 4 = (x ^ 2) ^ 2 by ring]
        rw [Real.sqrt_sq hx_sq_nonneg]
        rw [Real.sqrt_mul (sq_nonneg y)]
        rw [Real.sqrt_sq hy]
        rw [show z ^ 2 * w ^ 2 = (z * w) ^ 2 by ring]
        rw [Real.sqrt_sq (mul_nonneg hz hw)]
    _ = Real.sqrt A * x ^ 2 * y * z * w := by ring

private theorem coarsePoincareRHSGradientExpanded_le_publicRHS
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C) (hC_energy : Real.sqrt 250 ≤ C)
    (hC_force :
      Real.sqrt 15000 *
          ((d : ℝ) *
            (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    Real.sqrt
      (250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
            (publicCoeffField Q a))⁻¹ *
          cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (forcedSolutionGradientField u)) +
        15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
            (publicCoeffField Q a))⁻¹) ^ 2 *
          ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
      coarsePoincareWithRHSGradientRHS ((d : ℝ) * C) Q a s g u := by
  let L : ℝ := lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
    (publicCoeffField Q a)
  let Lpub : ℝ := Ch02.lambdaSq Q (s / 2) (Ch02.MultiscaleExponent.finite 2) a
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (forcedSolutionGradientField u))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let D : ℝ :=
    (d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2)
  have hs_le : s ≤ 1 := hs_lt.le
  have hs_half : 0 < s / 2 := by nlinarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact
      multiscale_ellipticity_lambdaSq_finite_nonneg
        Q (s / 2) 2 (publicCoeffField Q a)
        (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 ≤ (s / 2) * (2 : ℝ))
  have hL_inv_nonneg : 0 ≤ L⁻¹ := inv_nonneg.mpr hL_nonneg
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hE_nonneg : 0 ≤ E := by
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (forcedSolutionGradientField u))
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
      exact rpow_three_nat_add_le_nat_add_one d hs_le
    have hinner :
        Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2 ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg 2)
    exact mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.zero_le d)
  have hs_inv_le :
      s⁻¹ ≤ Real.rpow s (-(3 / 2 : ℝ)) := by
    exact inv_le_rpow_neg_three_halves hs hs_le
  have hs_inv_sq_eq : (s⁻¹) ^ 2 = Real.rpow s (-(2 : ℝ)) := by
    calc
      (s⁻¹) ^ 2 = (Real.rpow s (-1 : ℝ)) ^ 2 := by
        exact congrArg (fun x : ℝ => x ^ 2) (Real.rpow_neg_one s).symm
      _ = Real.rpow (Real.rpow s (-1 : ℝ)) (2 : ℝ) := by
        exact (Real.rpow_natCast (Real.rpow s (-1 : ℝ)) 2).symm
      _ = Real.rpow s ((-1 : ℝ) * (2 : ℝ)) := by
        exact (Real.rpow_mul hs.le (-1 : ℝ) (2 : ℝ)).symm
      _ = Real.rpow s (-(2 : ℝ)) := by ring_nf
  have hs_inv_sq_le :
      (s⁻¹) ^ 2 ≤ Real.rpow s (-3 : ℝ) := by
    calc
      (s⁻¹) ^ 2 = Real.rpow s (-(2 : ℝ)) := hs_inv_sq_eq
      _ ≤ Real.rpow s (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hs hs_le (by norm_num)
  have hA_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 * L⁻¹ * E := by
    positivity
  have hF_nonneg :
      0 ≤ 15000 * (s⁻¹) ^ 4 * (L⁻¹) ^ 2 * D ^ 2 * B ^ 2 := by
    positivity
  have hsqrtA :
      Real.sqrt (250 * (s⁻¹) ^ 2 * L⁻¹ * E) =
        Real.sqrt 250 * s⁻¹ * Real.sqrt L⁻¹ * Real.sqrt E := by
    calc
      Real.sqrt (250 * (s⁻¹) ^ 2 * L⁻¹ * E)
          = Real.sqrt (250 * ((s⁻¹) ^ 2 * (L⁻¹ * E))) := by ring_nf
      _ = Real.sqrt 250 * Real.sqrt ((s⁻¹) ^ 2 * (L⁻¹ * E)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 250)]
      _ = Real.sqrt 250 *
            (Real.sqrt ((s⁻¹) ^ 2) * Real.sqrt (L⁻¹ * E)) := by
        rw [Real.sqrt_mul (sq_nonneg s⁻¹)]
      _ = Real.sqrt 250 * (s⁻¹ * (Real.sqrt L⁻¹ * Real.sqrt E)) := by
        rw [Real.sqrt_sq hs_inv_nonneg, Real.sqrt_mul hL_inv_nonneg]
      _ = Real.sqrt 250 * s⁻¹ * Real.sqrt L⁻¹ * Real.sqrt E := by ring
  have hsqrtF :
      Real.sqrt (15000 * (s⁻¹) ^ 4 * (L⁻¹) ^ 2 * D ^ 2 * B ^ 2) =
        Real.sqrt 15000 * (s⁻¹) ^ 2 * L⁻¹ * D * B := by
    exact sqrt_const_mul_fourth_mul_sq_mul_sq_mul_sq
      (by norm_num : (0 : ℝ) ≤ 15000) hL_inv_nonneg hD_nonneg hB_nonneg
  have henergy_coeff :
      Real.sqrt 250 * s⁻¹ ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) := by
    exact mul_le_mul hC_energy hs_inv_le hs_inv_nonneg hC_nonneg
  have henergy_term :
      Real.sqrt 250 * s⁻¹ * Real.sqrt L⁻¹ * Real.sqrt E ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt L⁻¹ *
          Real.sqrt E := by
    have htail :
        0 ≤ Real.sqrt L⁻¹ * Real.sqrt E :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      Real.sqrt 250 * s⁻¹ * Real.sqrt L⁻¹ * Real.sqrt E
          = (Real.sqrt 250 * s⁻¹) * (Real.sqrt L⁻¹ * Real.sqrt E) := by ring
      _ ≤
          (C * Real.rpow s (-(3 / 2 : ℝ))) *
            (Real.sqrt L⁻¹ * Real.sqrt E) :=
          mul_le_mul_of_nonneg_right henergy_coeff htail
      _ = C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt L⁻¹ *
          Real.sqrt E := by ring
  have hforce_coeff_bound :
      Real.sqrt 15000 * D ≤ C := by
    calc
      Real.sqrt 15000 * D ≤
          Real.sqrt 15000 *
            ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left hD_le (Real.sqrt_nonneg 15000)
      _ = Real.sqrt 15000 *
          ((d : ℝ) *
            (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) := rfl
      _ ≤ C := hC_force
  have hforce_coeff :
      (Real.sqrt 15000 * D) * (s⁻¹) ^ 2 ≤
        C * Real.rpow s (-3 : ℝ) := by
    exact mul_le_mul hforce_coeff_bound hs_inv_sq_le
      (sq_nonneg s⁻¹) hC_nonneg
  have hforce_term :
      Real.sqrt 15000 * (s⁻¹) ^ 2 * L⁻¹ * D * B ≤
        C * Real.rpow s (-3 : ℝ) * L⁻¹ * B := by
    have htail : 0 ≤ L⁻¹ * B := mul_nonneg hL_inv_nonneg hB_nonneg
    calc
      Real.sqrt 15000 * (s⁻¹) ^ 2 * L⁻¹ * D * B
          = ((Real.sqrt 15000 * D) * (s⁻¹) ^ 2) * (L⁻¹ * B) := by ring
      _ ≤ (C * Real.rpow s (-3 : ℝ)) * (L⁻¹ * B) :=
          mul_le_mul_of_nonneg_right hforce_coeff htail
      _ = C * Real.rpow s (-3 : ℝ) * L⁻¹ * B := by ring
  have hsqrtL_public :
      Real.sqrt L⁻¹ ≤
        (d : ℝ) *
          poincareLowerEllipticityFactor Q a (s / 2)
            (Ch02.MultiscaleExponent.finite 2) := by
    simpa [L] using
      sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
        Q a hs_half
  have hL_inv_public :
      L⁻¹ ≤ (d : ℝ) * Real.rpow Lpub (-1 : ℝ) := by
    simpa [L, Lpub] using
      lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_public_rpow_neg_one
        Q a hs_half
  have henergy_public :
      C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt L⁻¹ * Real.sqrt E ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) *
          ((d : ℝ) *
            poincareLowerEllipticityFactor Q a (s / 2)
              (Ch02.MultiscaleExponent.finite 2)) * Real.sqrt E := by
    have hcoeff_nonneg :
        0 ≤ C * Real.rpow s (-(3 / 2 : ℝ)) :=
      mul_nonneg hC_nonneg (Real.rpow_nonneg hs.le _)
    have htail :
        Real.sqrt L⁻¹ * Real.sqrt E ≤
          ((d : ℝ) *
            poincareLowerEllipticityFactor Q a (s / 2)
              (Ch02.MultiscaleExponent.finite 2)) * Real.sqrt E :=
      mul_le_mul_of_nonneg_right hsqrtL_public (Real.sqrt_nonneg E)
    calc
      C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt L⁻¹ * Real.sqrt E
          =
        (C * Real.rpow s (-(3 / 2 : ℝ))) *
          (Real.sqrt L⁻¹ * Real.sqrt E) := by ring
      _ ≤
        (C * Real.rpow s (-(3 / 2 : ℝ))) *
          (((d : ℝ) *
            poincareLowerEllipticityFactor Q a (s / 2)
              (Ch02.MultiscaleExponent.finite 2)) * Real.sqrt E) :=
          mul_le_mul_of_nonneg_left htail hcoeff_nonneg
      _ =
        C * Real.rpow s (-(3 / 2 : ℝ)) *
          ((d : ℝ) *
            poincareLowerEllipticityFactor Q a (s / 2)
              (Ch02.MultiscaleExponent.finite 2)) * Real.sqrt E := by ring
  have hforce_public :
      C * Real.rpow s (-3 : ℝ) * L⁻¹ * B ≤
        C * Real.rpow s (-3 : ℝ) *
          ((d : ℝ) * Real.rpow Lpub (-1 : ℝ)) * B := by
    have hcoeff_nonneg : 0 ≤ C * Real.rpow s (-3 : ℝ) :=
      mul_nonneg hC_nonneg (Real.rpow_nonneg hs.le _)
    have htail :
        L⁻¹ * B ≤ ((d : ℝ) * Real.rpow Lpub (-1 : ℝ)) * B :=
      mul_le_mul_of_nonneg_right hL_inv_public hB_nonneg
    calc
      C * Real.rpow s (-3 : ℝ) * L⁻¹ * B
          = (C * Real.rpow s (-3 : ℝ)) * (L⁻¹ * B) := by ring
      _ ≤
          (C * Real.rpow s (-3 : ℝ)) *
            (((d : ℝ) * Real.rpow Lpub (-1 : ℝ)) * B) :=
          mul_le_mul_of_nonneg_left htail hcoeff_nonneg
      _ =
          C * Real.rpow s (-3 : ℝ) *
            ((d : ℝ) * Real.rpow Lpub (-1 : ℝ)) * B := by ring
  calc
    Real.sqrt
      (250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
            (publicCoeffField Q a))⁻¹ *
          cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (forcedSolutionGradientField u)) +
        15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (MultiscaleExponent.finite 2)
            (publicCoeffField Q a))⁻¹) ^ 2 *
          ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
        =
      Real.sqrt
        (250 * (s⁻¹) ^ 2 * L⁻¹ * E +
          15000 * (s⁻¹) ^ 4 * (L⁻¹) ^ 2 * D ^ 2 * B ^ 2) := by
        rfl
    _ ≤
      Real.sqrt (250 * (s⁻¹) ^ 2 * L⁻¹ * E) +
        Real.sqrt (15000 * (s⁻¹) ^ 4 * (L⁻¹) ^ 2 * D ^ 2 * B ^ 2) :=
        sqrt_add_le_add_sqrt_of_nonneg hA_nonneg hF_nonneg
    _ =
      Real.sqrt 250 * s⁻¹ * Real.sqrt L⁻¹ * Real.sqrt E +
        Real.sqrt 15000 * (s⁻¹) ^ 2 * L⁻¹ * D * B := by
        rw [hsqrtA, hsqrtF]
    _ ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt L⁻¹ * Real.sqrt E +
        C * Real.rpow s (-3 : ℝ) * L⁻¹ * B :=
        add_le_add henergy_term hforce_term
    _ ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) *
          ((d : ℝ) *
            poincareLowerEllipticityFactor Q a (s / 2)
              (Ch02.MultiscaleExponent.finite 2)) * Real.sqrt E +
        C * Real.rpow s (-3 : ℝ) *
          ((d : ℝ) * Real.rpow Lpub (-1 : ℝ)) * B :=
        add_le_add henergy_public hforce_public
    _ =
      coarsePoincareWithRHSGradientRHS ((d : ℝ) * C) Q a s g u := by
        unfold coarsePoincareWithRHSGradientRHS poincareLowerEllipticityFactor
        rw [← forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
          (Q := Q) (a := a) u]
        simp [Lpub]
        ring

/-- The deterministic zero-trace RHS energy envelope is bounded by the
note-facing public zero-Dirichlet RHS.  This algebraic bridge is reused by the
Dirichlet energy consequence, where the zero-boundary auxiliary solution is
constructed internally rather than supplied as a public `ZeroTraceForcedCubeSolution`. -/
theorem zeroTraceDirichletEnergyEnvelope_sqrt_le_publicRHS
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d}
    (ht : 0 < t) (ht_lt : t < 1 / 2)
    (hg : ForceBesovRegularity Q (2 * t) g) :
    Real.sqrt
        (_root_.Homogenization.zeroTraceDirichletEnergyEnvelope
          Q (publicCoeffField Q a) (2 * t) g) ≤
      zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a t g := by
  let L : ℝ := lambdaSq Q t (MultiscaleExponent.finite 2) (publicCoeffField Q a)
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q (2 * t) g
  let D : ℝ := (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + (2 * t))
  let K : ℝ := 250 + 2 * Real.sqrt 15000 * Real.sqrt 2
  have ht_le_one : t ≤ 1 := by nlinarith
  have htwo_t_pos : 0 < 2 * t := by nlinarith
  have htwo_t_le_one : 2 * t ≤ 1 := by nlinarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact
      multiscale_ellipticity_lambdaSq_finite_nonneg
        Q t 2 (publicCoeffField Q a)
        (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 ≤ t * (2 : ℝ))
  have hL_inv_nonneg : 0 ≤ L⁻¹ := inv_nonneg.mpr hL_nonneg
  have hB_nonneg : 0 ≤ B := by
    simpa [B, scaleNormalizedPositiveBesovVectorSeminormTwo] using
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := 2 * t) (g := g) hg
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hD_le :
      D ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
    dsimp [D]
    have hpow :
        Real.rpow (3 : ℝ) ((d : ℝ) + (2 * t)) ≤
          Real.rpow (3 : ℝ) ((d : ℝ) + 1) := by
      exact rpow_three_nat_add_le_nat_add_one d htwo_t_le_one
    exact mul_le_mul_of_nonneg_left hpow (by exact_mod_cast Nat.zero_le d)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hKsqrt_nonneg : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hconstD :
      Real.sqrt K * D ≤ C := by
    calc
      Real.sqrt K * D ≤
          Real.sqrt K * ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hD_le hKsqrt_nonneg
      _ ≤ C := by simpa [K] using hC_zero
  have htwo_t_inv_nonneg : 0 ≤ (2 * t)⁻¹ := inv_nonneg.mpr htwo_t_pos.le
  have htwo_t_inv_le :
      (2 * t)⁻¹ ≤ Real.rpow t (-(3 / 2 : ℝ)) := by
    have h1 : (2 * t)⁻¹ ≤ t⁻¹ := by
      simpa [one_div] using
        one_div_le_one_div_of_le ht (by nlinarith : t ≤ 2 * t)
    have h2 : t⁻¹ ≤ Real.rpow t (-(3 / 2 : ℝ)) := by
      exact inv_le_rpow_neg_three_halves ht ht_le_one
    exact h1.trans h2
  have hsqrtF :
      Real.sqrt
        (15000 * (2 * t)⁻¹ ^ 4 * L⁻¹ ^ 2 *
          (D * Real.sqrt 2) ^ 2 * B ^ 2) =
        Real.sqrt 15000 * (2 * t)⁻¹ ^ 2 * L⁻¹ *
          (D * Real.sqrt 2) * B := by
    exact sqrt_const_mul_fourth_mul_sq_mul_sq_mul_sq
      (by norm_num : (0 : ℝ) ≤ 15000) hL_inv_nonneg
      (mul_nonneg hD_nonneg (Real.sqrt_nonneg 2)) hB_nonneg
  have henv_eq :
      _root_.Homogenization.zeroTraceDirichletEnergyEnvelope
          Q (publicCoeffField Q a) (2 * t) g =
        K * D ^ 2 * (2 * t)⁻¹ ^ 2 * L⁻¹ * B ^ 2 := by
    have hraw :
        _root_.Homogenization.zeroTraceDirichletEnergyEnvelope
            Q (publicCoeffField Q a) (2 * t) g =
          (D * B) ^ 2 * (250 * (2 * t)⁻¹ ^ 2 * L⁻¹) +
            2 * |D * B| *
              Real.sqrt
                (15000 * (2 * t)⁻¹ ^ 4 * L⁻¹ ^ 2 *
                  (D * Real.sqrt 2) ^ 2 * B ^ 2) := by
      dsimp [D, B, L]
      unfold _root_.Homogenization.zeroTraceDirichletEnergyEnvelope
      simp only [lambdaSq]
      ring_nf
    have habs : |D * B| = D * B :=
      abs_of_nonneg (mul_nonneg hD_nonneg hB_nonneg)
    rw [hraw, habs, hsqrtF]
    dsimp [K]
    ring
  have hsqrt_prod :
      Real.sqrt (K * D ^ 2 * (2 * t)⁻¹ ^ 2 * L⁻¹ * B ^ 2) =
        Real.sqrt K * D * (2 * t)⁻¹ * Real.sqrt L⁻¹ * B := by
    calc
      Real.sqrt (K * D ^ 2 * (2 * t)⁻¹ ^ 2 * L⁻¹ * B ^ 2)
          =
        Real.sqrt
          (K * (D ^ 2 * ((2 * t)⁻¹ ^ 2 * (L⁻¹ * B ^ 2)))) := by
          ring_nf
      _ =
        Real.sqrt K *
          Real.sqrt (D ^ 2 * ((2 * t)⁻¹ ^ 2 * (L⁻¹ * B ^ 2))) := by
          rw [Real.sqrt_mul hK_nonneg]
      _ =
        Real.sqrt K *
          (Real.sqrt (D ^ 2) *
            Real.sqrt ((2 * t)⁻¹ ^ 2 * (L⁻¹ * B ^ 2))) := by
          rw [Real.sqrt_mul (sq_nonneg D)]
      _ =
        Real.sqrt K *
          (D * (Real.sqrt ((2 * t)⁻¹ ^ 2) *
            Real.sqrt (L⁻¹ * B ^ 2))) := by
          rw [Real.sqrt_sq hD_nonneg]
          rw [Real.sqrt_mul (sq_nonneg (2 * t)⁻¹)]
      _ =
        Real.sqrt K *
          (D * ((2 * t)⁻¹ * (Real.sqrt L⁻¹ * Real.sqrt (B ^ 2)))) := by
          rw [Real.sqrt_sq htwo_t_inv_nonneg]
          rw [Real.sqrt_mul hL_inv_nonneg]
      _ =
        Real.sqrt K * (D * ((2 * t)⁻¹ * (Real.sqrt L⁻¹ * B))) := by
          rw [Real.sqrt_sq hB_nonneg]
      _ = Real.sqrt K * D * (2 * t)⁻¹ * Real.sqrt L⁻¹ * B := by ring
  have hsqrtL_public :
      Real.sqrt L⁻¹ ≤
        (d : ℝ) *
          poincareLowerEllipticityFactor Q a t (Ch02.MultiscaleExponent.finite 2) := by
    simpa [L] using
      sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
        Q a ht
  have htail : 0 ≤ Real.sqrt L⁻¹ * B :=
    mul_nonneg (Real.sqrt_nonneg _) hB_nonneg
  have hpublic_tail :
      Real.sqrt L⁻¹ * B ≤
        ((d : ℝ) *
          poincareLowerEllipticityFactor Q a t (Ch02.MultiscaleExponent.finite 2)) * B :=
    mul_le_mul_of_nonneg_right hsqrtL_public hB_nonneg
  have hcoeff :
      (Real.sqrt K * D) * (2 * t)⁻¹ ≤
        C * Real.rpow t (-(3 / 2 : ℝ)) := by
    exact mul_le_mul hconstD htwo_t_inv_le htwo_t_inv_nonneg hC_nonneg
  have hcoeff_public_nonneg : 0 ≤ C * Real.rpow t (-(3 / 2 : ℝ)) :=
    mul_nonneg hC_nonneg (Real.rpow_nonneg ht.le _)
  calc
    Real.sqrt
        (_root_.Homogenization.zeroTraceDirichletEnergyEnvelope
          Q (publicCoeffField Q a) (2 * t) g)
        =
      Real.sqrt (K * D ^ 2 * (2 * t)⁻¹ ^ 2 * L⁻¹ * B ^ 2) := by
        rw [henv_eq]
    _ =
      Real.sqrt K * D * (2 * t)⁻¹ * Real.sqrt L⁻¹ * B := hsqrt_prod
    _ =
      (Real.sqrt K * D) * (2 * t)⁻¹ * (Real.sqrt L⁻¹ * B) := by ring
    _ ≤
      (C * Real.rpow t (-(3 / 2 : ℝ))) * (Real.sqrt L⁻¹ * B) :=
        mul_le_mul_of_nonneg_right hcoeff htail
    _ ≤
      (C * Real.rpow t (-(3 / 2 : ℝ))) *
        (((d : ℝ) *
          poincareLowerEllipticityFactor Q a t (Ch02.MultiscaleExponent.finite 2)) * B) :=
        mul_le_mul_of_nonneg_left hpublic_tail hcoeff_public_nonneg
    _ =
      zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a t g := by
        unfold zeroDirichletEnergyWithRHSRHS poincareLowerEllipticityFactor
        simp [B, scaleNormalizedPositiveBesovVectorSeminormTwo]
        ring

/-- Public theorem package for the coarse-grained Poincare estimate with
right-hand side, together with the auxiliary zero-Dirichlet energy estimate. -/
structure CoarsePoincareRHSTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g),
        0 < s → s < 1 → ForceBesovRegularity Q s g →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2)
              (forcedSolutionGradientField u) ≤
            coarsePoincareWithRHSGradientRHS C Q a s g u) ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d} (v : ZeroTraceForcedCubeSolution Q a g),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q (2 * t) g →
          zeroTraceForcedSolutionEnergyNorm Q a v ≤
            zeroDirichletEnergyWithRHSRHS C Q a t g)

/-- Public theorem package for the coarse-grained Poincare estimate with
right-hand side and the auxiliary zero-Dirichlet energy estimate. -/
theorem coarsePoincareRHSTheory {d : ℕ} [NeZero d] :
    CoarsePoincareRHSTheory d where
  exists_constant := by
    let CgradEnergy : ℝ := Real.sqrt 250
    let CgradForce : ℝ :=
      Real.sqrt 15000 *
        ((d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2))
    let Czero : ℝ :=
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
        ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1))
    let Cbase : ℝ := max 1 (max (max CgradEnergy CgradForce) Czero)
    let C : ℝ := (d : ℝ) * Cbase
    have hCbase_pos : 0 < Cbase := by
      exact lt_of_lt_of_le zero_lt_one
        (le_max_left 1 (max (max CgradEnergy CgradForce) Czero))
    have hCbase_nonneg : 0 ≤ Cbase := hCbase_pos.le
    have hC_pos : 0 < C := by
      dsimp [C]
      have hd_pos : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      exact mul_pos hd_pos hCbase_pos
    have hC_energy : Real.sqrt 250 ≤ Cbase := by
      calc
        Real.sqrt 250 = CgradEnergy := rfl
        _ ≤ max CgradEnergy CgradForce := le_max_left _ _
        _ ≤ max (max CgradEnergy CgradForce) Czero := le_max_left _ _
        _ ≤ Cbase := le_max_right _ _
    have hC_force :
        Real.sqrt 15000 *
            ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2)) ≤ Cbase := by
      calc
        Real.sqrt 15000 *
            ((d : ℝ) *
              (Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Real.sqrt 2))
            = CgradForce := rfl
        _ ≤ max CgradEnergy CgradForce := le_max_right _ _
        _ ≤ max (max CgradEnergy CgradForce) Czero := le_max_left _ _
        _ ≤ Cbase := le_max_right _ _
    have hC_zero :
        Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
            ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ Cbase := by
      calc
        Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
            ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1))
            = Czero := rfl
        _ ≤ max (max CgradEnergy CgradForce) Czero := le_max_right _ _
        _ ≤ Cbase := le_max_right _ _
    refine ⟨C, hC_pos, ?_, ?_⟩
    · intro Q a s g u hs hs_lt hg
      have hdet :=
        _root_.Homogenization.cubeBesovNegativeVectorSeminormTwo_grad_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_h1DirichletRhsWeakSolutionOn_of_cubeVectorBesovHRegularity
          (Q := Q) (a := publicCoeffField Q a) (g := g)
          (u := publicH1ToCubeSet u.toH1)
          (s := s) (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
          hs hs_lt.le (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
          (isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
            u.weakSolution)
          hg
      have hpub :=
        coarsePoincareRHSGradientExpanded_le_publicRHS
          (d := d) (C := Cbase) hCbase_nonneg hC_energy hC_force u hs hs_lt hg
      rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
      have hmain := hdet.trans (by simpa [C, forcedSolutionGradientField] using hpub)
      simpa [forcedSolutionGradientField] using hmain
    · intro Q a t g v ht ht_lt hg
      have htwo_t_pos : 0 < 2 * t := by nlinarith
      have htwo_t_le_one : 2 * t ≤ 1 := by nlinarith
      have hdet :=
        _root_.Homogenization.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded_of_isZeroTraceDirichletRhsWeakSolution_of_cubeVectorBesovHRegularity
          (Q := Q) (a := publicCoeffField Q a) (g := g)
          (v := publicH10ToCubeSet v.toH10)
          (s := 2 * t) (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
          htwo_t_pos htwo_t_le_one (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
          (isZeroTraceDirichletRhsWeakSolution_publicCoeffField_cubeSet_of_zeroTraceForcedCubeSolution
            v)
          hg
      have henergy :
          cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                v.toH10.toH1Function.grad) ≤
            _root_.Homogenization.zeroTraceDirichletEnergyEnvelope
              Q (publicCoeffField Q a) (2 * t) g := by
        simpa using hdet
      rw [zeroTraceForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField]
      exact (Real.sqrt_le_sqrt henergy).trans
        (zeroTraceDirichletEnergyEnvelope_sqrt_le_publicRHS
          (d := d) (C := Cbase) hCbase_nonneg hC_zero ht ht_lt hg)

end

end Ch03
end Book
end Homogenization
