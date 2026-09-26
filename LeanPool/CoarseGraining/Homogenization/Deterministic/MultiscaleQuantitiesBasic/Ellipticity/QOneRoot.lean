/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.EllipticityFiniteQ
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences

/-! # QOne Root -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped Matrix.Norms.Frobenius
open scoped MatrixOrder

/-!
# q = 1 ellipticity and localization
-/

theorem sqrt_coarseBBlockNorm_le_sqrt_maxDescendantBBlockNormAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d)
    (hR : R ∈ descendantsAtScale Q k) :
    Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
      Real.rpow (maxDescendantBBlockNormAtScale Q k a) (1 / 2 : ℝ) := by
  refine Real.rpow_le_rpow (coarseBBlockNorm_nonneg R a)
    (coarseBBlockNorm_le_maxDescendantBBlockNormAtScale a hR) ?_
  norm_num

theorem sqrt_coarseSigmaStarInvBlockNorm_le_sqrt_maxDescendantSigmaStarInvNormAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d)
    (hR : R ∈ descendantsAtScale Q k) :
    Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
      Real.rpow (maxDescendantSigmaStarInvNormAtScale Q k a) (1 / 2 : ℝ) := by
  refine Real.rpow_le_rpow (coarseSigmaStarInvBlockNorm_nonneg R a)
    (coarseSigmaStarInvBlockNorm_le_maxDescendantSigmaStarInvNormAtScale a hR) ?_
  norm_num

theorem geometricWeight_mul_sqrt_coarseBBlockNorm_le {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ) (n : ℕ)
    (hsq : 0 ≤ s * q) (hR : R ∈ descendantsAtScale Q k) :
    geometricWeight s q n * Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
      geometricWeight s q n * Real.rpow (maxDescendantBBlockNormAtScale Q k a) (1 / 2 : ℝ) := by
  exact mul_le_mul_of_nonneg_left
    (sqrt_coarseBBlockNorm_le_sqrt_maxDescendantBBlockNormAtScale a hR)
    (geometricWeight_nonneg n hsq)

theorem geometricWeight_mul_sqrt_coarseSigmaStarInvBlockNorm_le {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ) (n : ℕ)
    (hsq : 0 ≤ s * q) (hR : R ∈ descendantsAtScale Q k) :
    geometricWeight s q n * Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
      geometricWeight s q n * Real.rpow (maxDescendantSigmaStarInvNormAtScale Q k a) (1 / 2 : ℝ) := by
  exact mul_le_mul_of_nonneg_left
    (sqrt_coarseSigmaStarInvBlockNorm_le_sqrt_maxDescendantSigmaStarInvNormAtScale a hR)
    (geometricWeight_nonneg n hsq)

theorem weighted_sqrt_coarseBBlockNorm_le_LambdaSqFinite_one_series {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  have hk : k ≤ Q.scale := by
    by_contra hk
    exact (not_mem_descendantsAtScale_of_lt (Q := Q) (R := R) (k := k) (lt_of_not_ge hk)) hR
  let N : ℕ := Int.toNat (Q.scale - k)
  have hN : (N : ℤ) = Q.scale - k := by
    dsimp [N]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hk_eq : Q.scale - (N : ℤ) = k := by
    rw [hN]
    ring
  have hR' : R ∈ descendantsAtScale Q (Q.scale - (N : ℤ)) := by
    simpa [hk_eq] using hR
  have hterm :
      geometricWeight s 1 N * Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
        geometricWeight s 1 N *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (N : ℤ)) a) (1 / 2 : ℝ) := by
    exact geometricWeight_mul_sqrt_coarseBBlockNorm_le
      (a := a) (s := s) (q := 1) (n := N) (by simpa using hs) hR'
  have hnonneg :
      ∀ n : ℕ,
        0 ≤
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsingleton :
      ∑ n ∈ ({N} : Finset ℕ),
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
    exact hsum.sum_le_tsum ({N} : Finset ℕ) (fun n _ => hnonneg n)
  exact le_trans hterm (by simpa [N] using hsingleton)

theorem weighted_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSqFinite_one_series {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) := by
  have hk : k ≤ Q.scale := by
    by_contra hk
    exact (not_mem_descendantsAtScale_of_lt (Q := Q) (R := R) (k := k) (lt_of_not_ge hk)) hR
  let N : ℕ := Int.toNat (Q.scale - k)
  have hN : (N : ℤ) = Q.scale - k := by
    dsimp [N]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hk_eq : Q.scale - (N : ℤ) = k := by
    rw [hN]
    ring
  have hR' : R ∈ descendantsAtScale Q (Q.scale - (N : ℤ)) := by
    simpa [hk_eq] using hR
  have hterm :
      geometricWeight s 1 N * Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
        geometricWeight s 1 N *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (N : ℤ)) a)
            (1 / 2 : ℝ) := by
    exact geometricWeight_mul_sqrt_coarseSigmaStarInvBlockNorm_le
      (a := a) (s := s) (q := 1) (n := N) (by simpa using hs) hR'
  have hnonneg :
      ∀ n : ℕ,
        0 ≤
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsingleton :
      ∑ n ∈ ({N} : Finset ℕ),
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) := by
    exact hsum.sum_le_tsum ({N} : Finset ℕ) (fun n _ => hnonneg n)
  exact le_trans hterm (by simpa [N] using hsingleton)

theorem weighted_sqrt_coarseBBlockNorm_le_LambdaSq_one_rpow_half {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  have hnonneg :
      ∀ n : ℕ,
        0 ≤
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hseries_nonneg :
      0 ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) :=
    tsum_nonneg hnonneg
  calc
    geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) :=
      weighted_sqrt_coarseBBlockNorm_le_LambdaSqFinite_one_series a s hs hR hsum
    _ = Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
      rw [multiscale_ellipticity_LambdaSq_one_formula]
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      symm
      simpa [Real.rpow_natCast, hhalf] using
        (Real.rpow_rpow_inv hseries_nonneg (show (2 : ℝ) ≠ 0 by norm_num))

theorem weighted_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSq_one_rpow_neg_half {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
      Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
  have hnonneg :
      ∀ n : ℕ,
        0 ≤
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hseries_nonneg :
      0 ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) :=
    tsum_nonneg hnonneg
  calc
    geometricWeight s 1 (Int.toNat (Q.scale - k)) *
        Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) :=
      weighted_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSqFinite_one_series a s hs hR hsum
    _ = Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
      rw [multiscale_ellipticity_lambdaSq_one_formula]
      have hhalf : (-1 / 2 : ℝ) = (-2 : ℝ)⁻¹ := by norm_num
      symm
      simpa [hhalf] using
        (Real.rpow_rpow_inv hseries_nonneg (show (-2 : ℝ) ≠ 0 by norm_num))

theorem geometricDiscount_mul_sqrt_coarseBBlockNorm_le_LambdaSqFinite_one_series {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    geometricDiscount s 1 * Real.rpow (coarseBBlockNorm Q a) (1 / 2 : ℝ) ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  simpa using weighted_sqrt_coarseBBlockNorm_le_LambdaSqFinite_one_series
    (Q := Q) (R := Q) (k := Q.scale) a s hs (by simp) hsum

theorem geometricDiscount_mul_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSqFinite_one_series
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    geometricDiscount s 1 * Real.rpow (coarseSigmaStarInvBlockNorm Q a) (1 / 2 : ℝ) ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) := by
  simpa using weighted_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSqFinite_one_series
    (Q := Q) (R := Q) (k := Q.scale) a s hs (by simp) hsum

theorem geometricDiscount_mul_sqrt_coarseBBlockNorm_le_LambdaSq_one_rpow_half {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    geometricDiscount s 1 * Real.rpow (coarseBBlockNorm Q a) (1 / 2 : ℝ) ≤
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  have hnonneg :
      ∀ n : ℕ,
        0 ≤
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hseries_nonneg :
      0 ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) :=
    tsum_nonneg hnonneg
  calc
    geometricDiscount s 1 * Real.rpow (coarseBBlockNorm Q a) (1 / 2 : ℝ) ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) :=
      geometricDiscount_mul_sqrt_coarseBBlockNorm_le_LambdaSqFinite_one_series Q a s hs hsum
    _ = Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
      rw [multiscale_ellipticity_LambdaSq_one_formula]
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      symm
      simpa [Real.rpow_natCast, hhalf] using
        (Real.rpow_rpow_inv hseries_nonneg (show (2 : ℝ) ≠ 0 by norm_num))

theorem geometricDiscount_mul_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSq_one_rpow_neg_half
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    geometricDiscount s 1 * Real.rpow (coarseSigmaStarInvBlockNorm Q a) (1 / 2 : ℝ) ≤
      Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
  have hnonneg :
      ∀ n : ℕ,
        0 ≤
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hseries_nonneg :
      0 ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) :=
    tsum_nonneg hnonneg
  calc
    geometricDiscount s 1 * Real.rpow (coarseSigmaStarInvBlockNorm Q a) (1 / 2 : ℝ) ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) :=
      geometricDiscount_mul_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSqFinite_one_series Q a s hs
        hsum
    _ = Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
      rw [multiscale_ellipticity_lambdaSq_one_formula]
      have hhalf : (-1 / 2 : ℝ) = (-2 : ℝ)⁻¹ := by norm_num
      symm
      simpa [hhalf] using
        (Real.rpow_rpow_inv hseries_nonneg (show (-2 : ℝ) ≠ 0 by norm_num))

theorem multiscale_ellipticity_LambdaSq_one_series_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (hs : 0 ≤ s) :
    0 ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  refine tsum_nonneg ?_
  intro n
  refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
  refine Real.rpow_nonneg ?_ _
  exact maxDescendantBBlockNormAtScale_nonneg Q
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_lambdaSq_one_series_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (hs : 0 ≤ s) :
    0 ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  refine tsum_nonneg ?_
  intro n
  refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
  refine Real.rpow_nonneg ?_ _
  exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_LambdaSq_one_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (hs : 0 ≤ s) :
    0 ≤ LambdaSq Q s (.finite 1) a := by
  rw [multiscale_ellipticity_LambdaSq_one_formula]
  exact Real.rpow_nonneg
    (multiscale_ellipticity_LambdaSq_one_series_nonneg Q s a hs) _

theorem multiscale_ellipticity_lambdaSq_one_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (hs : 0 ≤ s) :
    0 ≤ lambdaSq Q s (.finite 1) a := by
  rw [multiscale_ellipticity_lambdaSq_one_formula]
  exact Real.rpow_nonneg
    (multiscale_ellipticity_lambdaSq_one_series_nonneg Q s a hs) _

theorem matNorm_pos_of_posDef {d : ℕ} [NeZero d] {A : Mat d} (hA : A.PosDef) :
    0 < matNorm A := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hdiag : 0 < A i i := hA.diag_pos
  have hA_ne : A ≠ 0 := by
    intro hzero
    have hdiag_zero : A i i = 0 := by simp [hzero]
    linarith
  rw [matNorm_eq_norm]
  exact norm_pos_iff.mpr hA_ne

theorem coarseBBlockNorm_pos_of_isEllipticFieldOn_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDeterministicCoarseData Q a) :
    0 < coarseBBlockNorm Q a := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hvol : (MeasureTheory.volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hpos :
      (bCoarse (sigmaCoarse (openCubeSet Q) a)
        (sigmaStarCoarse (openCubeSet Q) a)
        (kappaCoarse (openCubeSet Q) a)).PosDef :=
    bCoarse_canonical_posDef_of_isEllipticFieldOn_of_isSobolevRegularDomain
      (U := openCubeSet Q) (a := a)
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain
      hEll hvol hA hS hK hSigma hdet
  have hcanon :
      bCoarse sigma sigmaStar kappa =
        bCoarse (sigmaCoarse (openCubeSet Q) a)
          (sigmaStarCoarse (openCubeSet Q) a)
          (kappaCoarse (openCubeSet Q) a) := by
    rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
      eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
      eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  unfold coarseBBlockNorm
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a,
    coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix
      hA hS hK hSigma hdet,
    hcanon]
  exact matNorm_pos_of_posDef hpos

theorem coarseSigmaStarInvBlockNorm_pos_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (hData : OpenCubeDeterministicCoarseData Q a) :
    0 < coarseSigmaStarInvBlockNorm Q a := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  have hpos : (sigmaStarInvCoarse (openCubeSet Q) a).PosDef :=
    sigmaStarInvCoarse_posDef_of_isSigmaStarCoarse (U := openCubeSet Q) (a := a) hS hdet
  have hcanon : sigmaStar⁻¹ = sigmaStarInvCoarse (openCubeSet Q) a := by
    symm
    rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  unfold coarseSigmaStarInvBlockNorm
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a,
    coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix
      hA hS hK hSigma hdet,
    hcanon]
  exact matNorm_pos_of_posDef hpos

theorem multiscale_ellipticity_LambdaSq_one_series_pos_of_isEllipticFieldOn_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    {lam Lam : ℝ} (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    0 <
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    dsimp [f]
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hf_zero_pos : 0 < f 0 := by
    have hweight : 0 < geometricWeight s 1 0 :=
      geometricWeight_pos 0 (by simpa using hs)
    have hmax : 0 < maxDescendantBBlockNormAtScale Q Q.scale a := by
      simpa using coarseBBlockNorm_pos_of_isEllipticFieldOn_of_openCubeData
        Q a hEll hData
    have hrpow :
        0 < Real.rpow (maxDescendantBBlockNormAtScale Q Q.scale a) (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hmax _
    dsimp [f]
    simpa using mul_pos hweight hrpow
  simpa [f] using hsum.tsum_pos hf_nonneg 0 hf_zero_pos

theorem multiscale_ellipticity_lambdaSq_one_series_pos_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (hs : 0 < s)
    (hData : OpenCubeDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    0 <
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2 : ℝ)
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    dsimp [f]
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hf_zero_pos : 0 < f 0 := by
    have hweight : 0 < geometricWeight s 1 0 :=
      geometricWeight_pos 0 (by simpa using hs)
    have hmax : 0 < maxDescendantSigmaStarInvNormAtScale Q Q.scale a := by
      simpa using coarseSigmaStarInvBlockNorm_pos_of_openCubeData Q a hData
    have hrpow :
        0 < Real.rpow (maxDescendantSigmaStarInvNormAtScale Q Q.scale a)
          (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hmax _
    dsimp [f]
    simpa using mul_pos hweight hrpow
  simpa [f] using hsum.tsum_pos hf_nonneg 0 hf_zero_pos

theorem multiscale_ellipticity_LambdaSq_one_pos_of_isEllipticFieldOn_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    {lam Lam : ℝ} (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    0 < LambdaSq Q s (.finite 1) a := by
  rw [multiscale_ellipticity_LambdaSq_one_formula]
  exact Real.rpow_pos_of_pos
    (multiscale_ellipticity_LambdaSq_one_series_pos_of_isEllipticFieldOn_of_openCubeData
      Q a hs hEll hData hsum) _

theorem multiscale_ellipticity_lambdaSq_one_pos_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (hs : 0 < s)
    (hData : OpenCubeDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    0 < lambdaSq Q s (.finite 1) a := by
  rw [multiscale_ellipticity_lambdaSq_one_formula]
  exact Real.rpow_pos_of_pos
    (multiscale_ellipticity_lambdaSq_one_series_pos_of_openCubeData Q a hs hData hsum) _

theorem thetaRatio_pos_of_isEllipticFieldOn_of_openCubeData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s t : ℝ}
    {lam Lam : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDeterministicCoarseData Q a)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    0 < ThetaRatio Q s t a := by
  rw [thetaRatio_eq_div]
  exact div_pos
    (multiscale_ellipticity_LambdaSq_one_pos_of_isEllipticFieldOn_of_openCubeData
      Q a hs hEll hData hBsum)
    (multiscale_ellipticity_lambdaSq_one_pos_of_openCubeData Q a ht hData hSigmaSum)

theorem sq_rpow_half_eq_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x (1 / 2 : ℝ)) ^ 2 = x := by
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  simpa [Real.rpow_natCast, hhalf] using
    (Real.rpow_inv_rpow hx (show (2 : ℝ) ≠ 0 by norm_num))

theorem sq_rpow_neg_half_eq_inv_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x (-1 / 2 : ℝ)) ^ 2 = x⁻¹ := by
  calc
    (Real.rpow x (-1 / 2 : ℝ)) ^ 2 =
        Real.rpow (Real.rpow x (-1 / 2 : ℝ)) (2 : ℝ) := by
      symm
      exact Real.rpow_natCast _ 2
    _ = Real.rpow x ((-1 / 2 : ℝ) * 2) := by
      simpa using (Real.rpow_mul hx (-1 / 2 : ℝ) (2 : ℝ)).symm
    _ = x⁻¹ := by
      norm_num
      rw [Real.rpow_neg_one]

theorem geometricDiscount_sq_mul_coarseBBlockNorm_le_LambdaSq_one {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    geometricDiscount s 1 ^ 2 * coarseBBlockNorm Q a ≤
      LambdaSq Q s (.finite 1) a := by
  have hhalf :=
    geometricDiscount_mul_sqrt_coarseBBlockNorm_le_LambdaSq_one_rpow_half
      Q a s hs.le hsum
  have hleft_nonneg :
      0 ≤ geometricDiscount s 1 * Real.rpow (coarseBBlockNorm Q a) (1 / 2 : ℝ) := by
    refine mul_nonneg (le_of_lt (geometricDiscount_pos (by simpa using hs))) ?_
    exact Real.rpow_nonneg (coarseBBlockNorm_nonneg Q a) _
  have hsq := pow_le_pow_left₀ hleft_nonneg hhalf 2
  calc
    geometricDiscount s 1 ^ 2 * coarseBBlockNorm Q a =
        (geometricDiscount s 1 * Real.rpow (coarseBBlockNorm Q a) (1 / 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_half_eq_self_of_nonneg (coarseBBlockNorm_nonneg Q a)]
    _ ≤ (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := hsq
    _ = LambdaSq Q s (.finite 1) a := by
      exact sq_rpow_half_eq_self_of_nonneg
        (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le)

theorem geometricDiscount_sq_mul_coarseSigmaStarInvBlockNorm_le_lambdaSq_one_inv {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    geometricDiscount s 1 ^ 2 * coarseSigmaStarInvBlockNorm Q a ≤
      (lambdaSq Q s (.finite 1) a)⁻¹ := by
  have hhalf :=
    geometricDiscount_mul_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSq_one_rpow_neg_half
      Q a s hs.le hsum
  have hleft_nonneg :
      0 ≤ geometricDiscount s 1 * Real.rpow (coarseSigmaStarInvBlockNorm Q a) (1 / 2 : ℝ) := by
    refine mul_nonneg (le_of_lt (geometricDiscount_pos (by simpa using hs))) ?_
    exact Real.rpow_nonneg (coarseSigmaStarInvBlockNorm_nonneg Q a) _
  have hsq := pow_le_pow_left₀ hleft_nonneg hhalf 2
  calc
    geometricDiscount s 1 ^ 2 * coarseSigmaStarInvBlockNorm Q a =
        (geometricDiscount s 1 *
          Real.rpow (coarseSigmaStarInvBlockNorm Q a) (1 / 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_half_eq_self_of_nonneg (coarseSigmaStarInvBlockNorm_nonneg Q a)]
    _ ≤ (Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := hsq
    _ = (lambdaSq Q s (.finite 1) a)⁻¹ := by
      exact sq_rpow_neg_half_eq_inv_of_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg Q s a hs.le)

theorem coarseBBlockNorm_le_LambdaSq_one_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    coarseBBlockNorm Q a ≤ LambdaSq Q s (.finite 1) a := by
  simpa using
    (coarseBBlockNorm_le_LambdaSq_finite_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (a := a) (s := s) (q := 1) hs (by norm_num) hEll hData hsum)

theorem coarseSigmaStarInvBlockNorm_le_lambdaSq_one_inv_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseSigmaStarInvBlockNorm Q a ≤ (lambdaSq Q s (.finite 1) a)⁻¹ := by
  simpa using
    (coarseSigmaStarInvBlockNorm_le_lambdaSq_finite_inv_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (a := a) (s := s) (q := 1) hs (by norm_num) hEll hData hsum)

@[simp] theorem multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (hs : 0 ≤ s) :
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) =
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  rw [multiscale_ellipticity_LambdaSq_one_formula]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  simpa [Real.rpow_natCast, hhalf] using
    (Real.rpow_rpow_inv
      (multiscale_ellipticity_LambdaSq_one_series_nonneg Q s a hs)
      (show (2 : ℝ) ≠ 0 by norm_num))

@[simp] theorem multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (a : CoeffField d) (hs : 0 ≤ s) :
    Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) =
      ∑' n : ℕ,
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
  rw [multiscale_ellipticity_lambdaSq_one_formula]
  have hhalf : (-1 / 2 : ℝ) = (-2 : ℝ)⁻¹ := by norm_num
  simpa [hhalf] using
    (Real.rpow_rpow_inv
      (multiscale_ellipticity_lambdaSq_one_series_nonneg Q s a hs)
      (show (-2 : ℝ) ≠ 0 by norm_num))

theorem multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s : ℝ} {lam Lam : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤
      Real.rpow (LambdaSq Q t (.finite 1) a) (1 / 2 : ℝ) := by
  have hs : 0 < s := lt_trans ht hts
  rw [multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum Q s a hs.le,
    multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum Q t a ht.le]
  refine tsum_geometricWeight_one_le_of_monotone ?_ ?_ ht hts hsum_t
  · intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact maxDescendantBBlockNormAtScale_nonneg Q hlQ a
    · exact maxDescendantBBlockNormAtScale_le_of_le_of_isEllipticFieldOn_of_isSigmaCoarse
        (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ))
        hkl hlQ a hEll hData
    · norm_num
  · intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_LambdaSq_one_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s : ℝ} {lam Lam : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    LambdaSq Q s (.finite 1) a ≤ LambdaSq Q t (.finite 1) a := by
  have hs : 0 < s := lt_trans ht hts
  have hhalf :=
    multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a ht hts hEll hData hsum_t
  have hleft_nonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le) _
  have hsq := pow_le_pow_left₀ hleft_nonneg hhalf 2
  calc
    LambdaSq Q s (.finite 1) a =
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := by
          symm
          exact sq_rpow_half_eq_self_of_nonneg
            (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le)
    _ ≤ (Real.rpow (LambdaSq Q t (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := hsq
    _ = LambdaSq Q t (.finite 1) a := by
          exact sq_rpow_half_eq_self_of_nonneg
            (multiscale_ellipticity_LambdaSq_one_nonneg Q t a ht.le)

theorem multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s : ℝ} {lam Lam : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) ≤
      Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) := by
  have hs : 0 < s := lt_trans ht hts
  rw [multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum Q s a hs.le,
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum Q t a ht.le]
  refine tsum_geometricWeight_one_le_of_monotone ?_ ?_ ht hts hsum_t
  · intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact maxDescendantSigmaStarInvNormAtScale_nonneg Q hlQ a
    · exact maxDescendantSigmaStarInvNormAtScale_le_of_le_of_isEllipticFieldOn_of_isSigmaCoarse
        (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ))
        hkl hlQ a hEll hData
    · norm_num
  · intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_lambdaSq_one_inv_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s : ℝ} {lam Lam : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    (lambdaSq Q s (.finite 1) a)⁻¹ ≤ (lambdaSq Q t (.finite 1) a)⁻¹ := by
  have hs : 0 < s := lt_trans ht hts
  have hhalf :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a ht hts hEll hData hsum_t
  have hleft_nonneg :
      0 ≤ Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_lambdaSq_one_nonneg Q s a hs.le) _
  have hsq := pow_le_pow_left₀ hleft_nonneg hhalf 2
  calc
    (lambdaSq Q s (.finite 1) a)⁻¹ =
        (Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
          symm
          exact sq_rpow_neg_half_eq_inv_of_nonneg
            (multiscale_ellipticity_lambdaSq_one_nonneg Q s a hs.le)
    _ ≤ (Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := hsq
    _ = (lambdaSq Q t (.finite 1) a)⁻¹ := by
          exact sq_rpow_neg_half_eq_inv_of_nonneg
            (multiscale_ellipticity_lambdaSq_one_nonneg Q t a ht.le)


end

end Homogenization
