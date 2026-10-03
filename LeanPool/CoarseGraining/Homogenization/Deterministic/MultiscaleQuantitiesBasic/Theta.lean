/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity

/-! # Theta -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped Matrix.Norms.Frobenius
open scoped MatrixOrder

/-!
# Boundary-facing theta statements
-/

theorem thetaRatio_boundary_coefficient_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : R ∈ descendantsAtScale Q k)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    Real.rpow (3 : ℝ) (-(Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (-(1 - s - t) * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  have htheta :=
    thetaRatio_rpow_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s t hs ht hR hBsum hSigmaSum
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hfactorNonneg :
      0 ≤ Real.rpow (3 : ℝ) (-(h : ℝ)) := by
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  calc
    Real.rpow (3 : ℝ) (-(h : ℝ)) * Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
        Real.rpow (3 : ℝ) (-(h : ℝ)) *
          (Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htheta hfactorNonneg
    _ =
        Real.rpow (3 : ℝ) (-(1 - s - t) * (h : ℝ)) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
      have hpow :
          Real.rpow (3 : ℝ) (-(h : ℝ)) * Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) =
            Real.rpow (3 : ℝ) (-(1 - s - t) * (h : ℝ)) := by
        calc
          Real.rpow (3 : ℝ) (-(h : ℝ)) * Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) =
              Real.rpow (3 : ℝ) (-(h : ℝ) + (s + t) * (h : ℝ)) := by
            simpa using (Real.rpow_add h3 (-(h : ℝ)) ((s + t) * (h : ℝ))).symm
          _ = Real.rpow (3 : ℝ) (-(1 - s - t) * (h : ℝ)) := by
            congr 1
            ring
      calc
        Real.rpow (3 : ℝ) (-(h : ℝ)) *
            (Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) *
              Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) =
          (Real.rpow (3 : ℝ) (-(h : ℝ)) * Real.rpow (3 : ℝ) ((s + t) * (h : ℝ))) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
          ring
        _ =
          Real.rpow (3 : ℝ) (-(1 - s - t) * (h : ℝ)) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
          rw [hpow]

theorem weighted_descendant_product_sq_le_thetaRatio {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : R ∈ descendantsAtScale Q k)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    ((geometricWeight s 1 (Int.toNat (Q.scale - k)) *
          Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ)) *
        (geometricWeight t 1 (Int.toNat (Q.scale - k)) *
          Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ))) ^ 2 ≤
      ThetaRatio Q s t a := by
  have hB :
      geometricWeight s 1 (Int.toNat (Q.scale - k)) *
          Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) :=
    weighted_sqrt_coarseBBlockNorm_le_LambdaSq_one_rpow_half
      (Q := Q) (R := R) (k := k) a s hs hR hBsum
  have hSigma :
      geometricWeight t 1 (Int.toNat (Q.scale - k)) *
          Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
        Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) :=
    weighted_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSq_one_rpow_neg_half
      (Q := Q) (R := R) (k := k) a t ht hR hSigmaSum
  have hBnonneg :
      0 ≤ geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) := by
    refine mul_nonneg (geometricWeight_nonneg _ (by simpa using hs)) ?_
    exact Real.rpow_nonneg (coarseBBlockNorm_nonneg R a) _
  have hSigmanonneg :
      0 ≤ geometricWeight t 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) := by
    refine mul_nonneg (geometricWeight_nonneg _ (by simpa using ht)) ?_
    exact Real.rpow_nonneg (coarseSigmaStarInvBlockNorm_nonneg R a) _
  have hLambdanonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs) _
  have hmul :
      (geometricWeight s 1 (Int.toNat (Q.scale - k)) *
          Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ)) *
        (geometricWeight t 1 (Int.toNat (Q.scale - k)) *
          Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ)) ≤
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) := by
    exact mul_le_mul hB hSigma hSigmanonneg hLambdanonneg
  have hprodNonneg :
      0 ≤
        (geometricWeight s 1 (Int.toNat (Q.scale - k)) *
            Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ)) *
          (geometricWeight t 1 (Int.toNat (Q.scale - k)) *
            Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ)) := by
    exact mul_nonneg hBnonneg hSigmanonneg
  have hsq := pow_le_pow_left₀ hprodNonneg hmul 2
  rw [thetaRatio_eq_sq_mul_rpow_half_rpow_neg_half Q s t a hs ht]
  exact hsq

end

end Homogenization
