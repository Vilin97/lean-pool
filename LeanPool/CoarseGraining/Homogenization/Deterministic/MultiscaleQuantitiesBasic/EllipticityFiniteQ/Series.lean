/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response

/-! # Series -/

namespace Homogenization

noncomputable section

open scoped Matrix.Norms.Frobenius
open scoped MatrixOrder

/-!
# Finite-q ellipticity and localization

This file upgrades the Chapter-2 ellipticity surface from the first `q = 1`
lane to the finite-`q` statements actually present in the notes.
-/

@[simp] theorem multiscale_ellipticity_LambdaSq_finite_formula {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) :
    LambdaSq Q s (.finite q) a =
      Real.rpow
        (∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
        (2 / q) := by
  rw [multiscale_ellipticity_LambdaSq_finite_eq]
  rfl

@[simp] theorem multiscale_ellipticity_lambdaSq_finite_formula {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) :
    lambdaSq Q s (.finite q) a =
      Real.rpow
        (∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
        (-2 / q) := by
  rw [multiscale_ellipticity_lambdaSq_finite_eq]
  rfl

theorem multiscale_ellipticity_LambdaSq_finite_series_nonneg {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) (_hq : 0 ≤ q) (hsq : 0 ≤ s * q) :
    0 ≤
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
  refine tsum_nonneg ?_
  intro n
  refine mul_nonneg (geometricWeight_nonneg n hsq) ?_
  refine Real.rpow_nonneg ?_ _
  exact maxDescendantBBlockNormAtScale_nonneg Q
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_lambdaSq_finite_series_nonneg {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) (_hq : 0 ≤ q) (hsq : 0 ≤ s * q) :
    0 ≤
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
  refine tsum_nonneg ?_
  intro n
  refine mul_nonneg (geometricWeight_nonneg n hsq) ?_
  refine Real.rpow_nonneg ?_ _
  exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
    (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_LambdaSq_finite_nonneg {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) (hq : 0 ≤ q) (hsq : 0 ≤ s * q) :
    0 ≤ LambdaSq Q s (.finite q) a := by
  rw [multiscale_ellipticity_LambdaSq_finite_formula]
  exact Real.rpow_nonneg
    (multiscale_ellipticity_LambdaSq_finite_series_nonneg Q s q a hq hsq) _

theorem multiscale_ellipticity_lambdaSq_finite_nonneg {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) (hq : 0 ≤ q) (hsq : 0 ≤ s * q) :
    0 ≤ lambdaSq Q s (.finite q) a := by
  rw [multiscale_ellipticity_lambdaSq_finite_formula]
  exact Real.rpow_nonneg
    (multiscale_ellipticity_lambdaSq_finite_series_nonneg Q s q a hq hsq) _

@[simp] theorem multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) (hq : 0 < q) (hsq : 0 ≤ s * q) :
    Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) =
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
  rw [multiscale_ellipticity_LambdaSq_finite_formula]
  let S : ℝ :=
    ∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact multiscale_ellipticity_LambdaSq_finite_series_nonneg Q s q a hq.le hsq
  have hmul : (2 / q : ℝ) * (q / 2) = 1 := by
    field_simp [hq.ne']
  calc
    Real.rpow (Real.rpow S (2 / q)) (q / 2) = Real.rpow S ((2 / q) * (q / 2)) := by
      symm
      exact Real.rpow_mul hS_nonneg (2 / q : ℝ) (q / 2)
    _ = Real.rpow S 1 := by simp [hmul]
    _ = S := by exact Real.rpow_one S
    _ = ∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
      rfl

@[simp] theorem multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (a : CoeffField d) (hq : 0 < q) (hsq : 0 ≤ s * q) :
    Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) =
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
  rw [multiscale_ellipticity_lambdaSq_finite_formula]
  let S : ℝ :=
    ∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact multiscale_ellipticity_lambdaSq_finite_series_nonneg Q s q a hq.le hsq
  have hmul : (-2 / q : ℝ) * (-q / 2) = 1 := by
    field_simp [hq.ne']
  calc
    Real.rpow (Real.rpow S (-2 / q)) (-q / 2) = Real.rpow S ((-2 / q) * (-q / 2)) := by
      symm
      exact Real.rpow_mul hS_nonneg (-2 / q : ℝ) (-q / 2)
    _ = Real.rpow S 1 := by simp [hmul]
    _ = S := by exact Real.rpow_one S
    _ = ∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (q / 2) := by
      rfl

private theorem le_of_rpow_q_div_two_le {A B q : ℝ} (hq : 0 < q)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : Real.rpow A (q / 2) ≤ Real.rpow B (q / 2)) :
    A ≤ B := by
  have hpow :
      Real.rpow (Real.rpow A (q / 2)) (2 / q) ≤
        Real.rpow (Real.rpow B (q / 2)) (2 / q) := by
    refine Real.rpow_le_rpow ?_ hAB ?_
    · exact Real.rpow_nonneg hA _
    · positivity
  have hmul : (q / 2 : ℝ) * (2 / q) = 1 := by
    field_simp [hq.ne']
  calc
    A = Real.rpow A 1 := by symm; exact Real.rpow_one A
    _ = Real.rpow (Real.rpow A (q / 2)) (2 / q) := by
          simpa [hmul] using (Real.rpow_mul hA (q / 2) (2 / q))
    _ ≤ Real.rpow (Real.rpow B (q / 2)) (2 / q) := hpow
    _ = Real.rpow B 1 := by
          simpa [hmul] using (Real.rpow_mul hB (q / 2) (2 / q)).symm
    _ = B := by exact Real.rpow_one B

theorem coarseBBlockNorm_rpow_q_div_two_le_LambdaSq_finite_rpow_q_div_two_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s q : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hq : 0 < q)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    Real.rpow (coarseBBlockNorm Q a) (q / 2) ≤
      Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
  let H : ℕ → ℝ := fun n =>
    Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  have hmono : Monotone H := by
    intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact maxDescendantBBlockNormAtScale_nonneg Q hlQ a
    · exact maxDescendantBBlockNormAtScale_le_of_le_of_isEllipticFieldOn_of_isSigmaCoarse
        (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ))
        hkl hlQ a hEll hData
    · positivity
  have hself :
      H 0 ≤
        ∑' n : ℕ, geometricWeight s q n * H n := by
    exact self_le_tsum_geometricWeight_of_monotone hmono
      (mul_pos hs hq) (by simpa [H] using hsum)
  calc
    Real.rpow (coarseBBlockNorm Q a) (q / 2) = H 0 := by
      dsimp [H]
      simp [maxDescendantBBlockNormAtScale, descendantsAtScale_self]
    _ ≤ ∑' n : ℕ, geometricWeight s q n * H n := hself
    _ = Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
      symm
      simpa [H] using
        (multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum Q s q a hq
          (mul_nonneg hs.le hq.le))

theorem coarseSigmaStarInvBlockNorm_rpow_q_div_two_le_lambdaSq_finite_rpow_neg_q_div_two_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s q : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hq : 0 < q)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    Real.rpow (coarseSigmaStarInvBlockNorm Q a) (q / 2) ≤
      Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
  let H : ℕ → ℝ := fun n =>
    Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  have hmono : Monotone H := by
    intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact maxDescendantSigmaStarInvNormAtScale_nonneg Q hlQ a
    · exact maxDescendantSigmaStarInvNormAtScale_le_of_le_of_isEllipticFieldOn_of_isSigmaCoarse
        (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ))
        hkl hlQ a hEll hData
    · positivity
  have hself :
      H 0 ≤
        ∑' n : ℕ, geometricWeight s q n * H n := by
    exact self_le_tsum_geometricWeight_of_monotone hmono
      (mul_pos hs hq) (by simpa [H] using hsum)
  calc
    Real.rpow (coarseSigmaStarInvBlockNorm Q a) (q / 2) = H 0 := by
      dsimp [H]
      simp [maxDescendantSigmaStarInvNormAtScale, descendantsAtScale_self]
    _ ≤ ∑' n : ℕ, geometricWeight s q n * H n := hself
    _ = Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
      symm
      simpa [H] using
        (multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum Q s q a hq
          (mul_nonneg hs.le hq.le))

theorem coarseBBlockNorm_le_LambdaSq_finite_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s q : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hq : 0 < q)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    coarseBBlockNorm Q a ≤ LambdaSq Q s (.finite q) a := by
  exact le_of_rpow_q_div_two_le hq
    (coarseBBlockNorm_nonneg Q a)
    (multiscale_ellipticity_LambdaSq_finite_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le))
    (coarseBBlockNorm_rpow_q_div_two_le_LambdaSq_finite_rpow_q_div_two_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hs hq hEll hData hsum)

theorem coarseSigmaStarInvBlockNorm_le_lambdaSq_finite_inv_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s q : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hq : 0 < q)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    coarseSigmaStarInvBlockNorm Q a ≤ (lambdaSq Q s (.finite q) a)⁻¹ := by
  have hpow :=
    coarseSigmaStarInvBlockNorm_rpow_q_div_two_le_lambdaSq_finite_rpow_neg_q_div_two_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hs hq hEll hData hsum
  have hlambda_nonneg :
      0 ≤ lambdaSq Q s (.finite q) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le)
  have hpow' :
      Real.rpow (coarseSigmaStarInvBlockNorm Q a) (q / 2) ≤
        Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
    calc
      Real.rpow (coarseSigmaStarInvBlockNorm Q a) (q / 2) ≤
          Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := hpow
      _ = Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
        have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
        simpa [hneg] using
          (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2))
  exact le_of_rpow_q_div_two_le hq
    (coarseSigmaStarInvBlockNorm_nonneg Q a)
    (inv_nonneg.mpr hlambda_nonneg)
    hpow'

theorem multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) ≤
      Real.rpow (LambdaSq Q t (.finite q) a) (q / 2) := by
  have hs : 0 < s := lt_trans ht hts
  rw [multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum Q s q a hq
      (mul_nonneg hs.le hq.le),
    multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum Q t q a hq
      (mul_nonneg ht.le hq.le)]
  refine tsum_geometricWeight_le_of_monotone ?_ ?_ hq ht hts hsum_t
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
    · positivity
  · intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_LambdaSq_finite_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    LambdaSq Q s (.finite q) a ≤ LambdaSq Q t (.finite q) a := by
  have hs : 0 < s := lt_trans ht hts
  exact le_of_rpow_q_div_two_le hq
    (multiscale_ellipticity_LambdaSq_finite_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le))
    (multiscale_ellipticity_LambdaSq_finite_nonneg Q t q a hq.le (mul_nonneg ht.le hq.le))
    (multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hq ht hts hEll hData hsum_t)

theorem multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) ≤
      Real.rpow (lambdaSq Q t (.finite q) a) (-q / 2) := by
  have hs : 0 < s := lt_trans ht hts
  rw [multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum Q s q a hq
      (mul_nonneg hs.le hq.le),
    multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum Q t q a hq
      (mul_nonneg ht.le hq.le)]
  refine tsum_geometricWeight_le_of_monotone ?_ ?_ hq ht hts hsum_t
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
    · positivity
  · intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a

theorem multiscale_ellipticity_lambdaSq_finite_inv_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    (lambdaSq Q s (.finite q) a)⁻¹ ≤ (lambdaSq Q t (.finite q) a)⁻¹ := by
  have hs : 0 < s := lt_trans ht hts
  have hpow :=
    multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hq ht hts hEll hData hsum_t
  have hpow' :
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) ≤
        Real.rpow ((lambdaSq Q t (.finite q) a)⁻¹) (q / 2) := by
    have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
    calc
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) =
          Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2)).symm
      _ ≤ Real.rpow (lambdaSq Q t (.finite q) a) (-q / 2) := hpow
      _ = Real.rpow ((lambdaSq Q t (.finite q) a)⁻¹) (q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q t (.finite q) a) (q / 2))
  exact le_of_rpow_q_div_two_le hq
    (inv_nonneg.mpr (multiscale_ellipticity_lambdaSq_finite_nonneg Q s q a hq.le
      (mul_nonneg hs.le hq.le)))
    (inv_nonneg.mpr (multiscale_ellipticity_lambdaSq_finite_nonneg Q t q a hq.le
      (mul_nonneg ht.le hq.le)))
    hpow'


end

end Homogenization
