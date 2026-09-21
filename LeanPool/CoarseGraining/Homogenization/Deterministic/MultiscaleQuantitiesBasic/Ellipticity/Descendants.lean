/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.QOneRoot

/-! # Descendants -/

namespace Homogenization

noncomputable section

theorem thetaRatio_eq_sq_mul_rpow_half_rpow_neg_half {d : ℕ}
    (Q : TriadicCube d) (s t : ℝ) (a : CoeffField d)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ThetaRatio Q s t a =
      (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
  have hLambda :
      (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 =
        LambdaSq Q s (.finite 1) a := by
    have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    simpa [Real.rpow_natCast, hhalf] using
      (Real.rpow_inv_rpow
        (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs)
        (show (2 : ℝ) ≠ 0 by norm_num))
  have hlambdaInv :
      (Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 =
        (lambdaSq Q t (.finite 1) a)⁻¹ := by
    let x := lambdaSq Q t (.finite 1) a
    have hx : 0 ≤ x := by
      dsimp [x]
      exact multiscale_ellipticity_lambdaSq_one_nonneg Q t a ht
    change (Real.rpow x (-1 / 2 : ℝ)) ^ 2 = x⁻¹
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
  rw [thetaRatio_eq_div, div_eq_mul_inv]
  calc
    LambdaSq Q s (.finite 1) a * (lambdaSq Q t (.finite 1) a)⁻¹ =
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 *
          (Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
      rw [hLambda, hlambdaInv]
    _ =
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      ring

theorem thetaRatio_eq_sq_series_product {d : ℕ}
    (Q : TriadicCube d) (s t : ℝ) (a : CoeffField d)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ThetaRatio Q s t a =
      ((∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) *
        (∑' n : ℕ,
          geometricWeight t 1 n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ))) ^ 2 := by
  rw [thetaRatio_eq_sq_mul_rpow_half_rpow_neg_half Q s t a hs ht]
  rw [multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum Q s a hs]
  rw [multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum Q t a ht]

theorem thetaRatio_nonneg {d : ℕ}
    (Q : TriadicCube d) (s t : ℝ) (a : CoeffField d)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ ThetaRatio Q s t a := by
  rw [thetaRatio_eq_sq_mul_rpow_half_rpow_neg_half Q s t a hs ht]
  exact sq_nonneg _

theorem thetaRatio_rpow_half_eq_mul_rpow_half_rpow_neg_half {d : ℕ}
    (Q : TriadicCube d) (s t : ℝ) (a : CoeffField d)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) =
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) := by
  rw [thetaRatio_eq_sq_mul_rpow_half_rpow_neg_half Q s t a hs ht]
  let x :=
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)
  have hLambdaNonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs) _
  have hlambdaNonneg :
      0 ≤ Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_lambdaSq_one_nonneg Q t a ht) _
  have hprodNonneg : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hLambdaNonneg hlambdaNonneg
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  change Real.rpow (x ^ 2) (1 / 2 : ℝ) = x
  simpa [Real.rpow_natCast, hhalf] using
    (Real.rpow_rpow_inv hprodNonneg (show (2 : ℝ) ≠ 0 by norm_num))

theorem multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have htailSummable : Summable (fun n : ℕ => fQ (n + h)) := (summable_nat_add_iff h).2 hsum
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hterm :
      ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hmax :
        maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a ≤
          maxDescendantBBlockNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a := by
      have hl : R.scale - (n : ℤ) ≤ R.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (maxDescendantBBlockNormAtScale_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a hR hl)
    have hrpow :
        Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (1 / 2 : ℝ) ≤
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a) (1 / 2 : ℝ) := by
      refine Real.rpow_le_rpow
        (maxDescendantBBlockNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      norm_num
    calc
      fR n =
          factor *
            (geometricWeight s 1 (n + h) *
              Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
        dsimp [fR, factor]
        rw [geometricWeight_one_shift (s := s) h n]
        simp [mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s 1 (n + h) *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
              (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow (geometricWeight_nonneg (n + h) (by simpa using hs))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hscaledNonneg : ∀ n : ℕ, 0 ≤ factor * fQ (n + h) := by
    intro n
    exact mul_nonneg hfactorNonneg (hQnonneg (n + h))
  have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  have hRsummable : Summable fR :=
    Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable
  have hsumLe :
      ∑' n : ℕ, fR n ≤ ∑' n : ℕ, factor * fQ (n + h) :=
    Summable.tsum_le_tsum hterm hRsummable hscaledSummable
  have htailLe :
      ∑' n : ℕ, fQ (n + h) ≤ ∑' n : ℕ, fQ n := by
    have hsplit := hsum.sum_add_tsum_nat_add h
    have hprefixNonneg : 0 ≤ ∑ i ∈ Finset.range h, fQ i := by
      exact Finset.sum_nonneg (fun i _ => hQnonneg i)
    linarith
  calc
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) = ∑' n : ℕ, fR n := by
      simpa [fR] using (multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum R s a hs)
    _ ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n := by
      exact mul_le_mul_of_nonneg_left htailLe hfactorNonneg
    _ = factor * Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
      simpa [fQ] using congrArg (fun x : ℝ => factor * x)
        (multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum Q s a hs).symm

/-- Convert a depth-`j` descendant membership into the corresponding
absolute-scale descendant membership. -/
theorem mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
  have hk : Q.scale - (j : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
    ring
  simpa [hdiff] using hR

/-- A summable upper-ellipticity `q = 1` series remains summable after
restricting the base cube to a descendant. -/
theorem summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have htailSummable : Summable (fun n : ℕ => fQ (n + h)) :=
    (summable_nat_add_iff h).2 hsum
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hterm :
      ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hmax :
        maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a ≤
          maxDescendantBBlockNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a := by
      have hl : R.scale - (n : ℤ) ≤ R.scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (maxDescendantBBlockNormAtScale_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a hR hl)
    have hrpow :
        Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) ≤
          Real.rpow
            (maxDescendantBBlockNormAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) a) (1 / 2 : ℝ) := by
      refine Real.rpow_le_rpow
        (maxDescendantBBlockNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      norm_num
    calc
      fR n =
          factor *
            (geometricWeight s 1 (n + h) *
              Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
        dsimp [fR, factor]
        rw [geometricWeight_one_shift (s := s) h n]
        simp [mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s 1 (n + h) *
            Real.rpow
              (maxDescendantBBlockNormAtScale Q
                (Q.scale - ((n + h : ℕ) : ℤ)) a) (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (geometricWeight_nonneg (n + h) (by simpa using hs))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  exact Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable

/-- Depth-`j` form of
`summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtScale`. -/
theorem summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a s hs
      (mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR) hsum

/-- Depth-`j` form of
`summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtScale`. -/
theorem
    summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a s (1 : ℝ) hs
      (by norm_num) (mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR) hsum

/-- Depth-`j` form of the finite-`q = 1` upper ellipticity localization. -/
theorem multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
      ring
    simp [hdiff]
  simpa [htoNat] using
    (multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a s hs hRscale hsum)

theorem multiscale_ellipticity_LambdaSq_one_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    LambdaSq R s (.finite 1) a ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        LambdaSq Q s (.finite 1) a := by
  have hhalf :=
    multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s hs hR hsum
  have hsqrt_nonneg :
      0 ≤ Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs) _
  have hsq := pow_le_pow_left₀ hsqrt_nonneg hhalf 2
  have hfactorSq :
      (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 =
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 =
          Real.rpow (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) ((s * (Int.toNat (Q.scale - k) : ℝ)) * 2) := by
        simpa using (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
          (s * (Int.toNat (Q.scale - k) : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) := by
        congr 1
        ring
  calc
    LambdaSq R s (.finite 1) a =
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := by
      symm
      exact sq_rpow_half_eq_self_of_nonneg
        (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs)
    _ ≤
        (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := hsq
    _ =
        (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 *
          LambdaSq Q s (.finite 1) a := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_half_eq_self_of_nonneg
        (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs)]
    _ = Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q s (.finite 1) a := by
      rw [hfactorSq]

theorem multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    Real.rpow (lambdaSq R s (.finite 1) a) (-1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a) (1 / 2 : ℝ)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have htailSummable : Summable (fun n : ℕ => fQ (n + h)) := (summable_nat_add_iff h).2 hsum
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hterm :
      ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hmax :
        maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a ≤
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a := by
      have hl : R.scale - (n : ℤ) ≤ R.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (maxDescendantSigmaStarInvNormAtScale_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a hR hl)
    have hrpow :
        Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a) (1 / 2 : ℝ) ≤
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
            (1 / 2 : ℝ) := by
      refine Real.rpow_le_rpow
        (maxDescendantSigmaStarInvNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      norm_num
    calc
      fR n =
          factor *
            (geometricWeight s 1 (n + h) *
              Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
        dsimp [fR, factor]
        rw [geometricWeight_one_shift (s := s) h n]
        simp [mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s 1 (n + h) *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
              (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow (geometricWeight_nonneg (n + h) (by simpa using hs))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hscaledNonneg : ∀ n : ℕ, 0 ≤ factor * fQ (n + h) := by
    intro n
    exact mul_nonneg hfactorNonneg (hQnonneg (n + h))
  have hRsummable : Summable fR := by
    have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
      htailSummable.mul_left factor
    have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
      intro n
      dsimp [fR]
      refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs)) ?_
      refine Real.rpow_nonneg ?_ _
      exact maxDescendantSigmaStarInvNormAtScale_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
    exact Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable
  have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  have hsumLe :
      ∑' n : ℕ, fR n ≤ ∑' n : ℕ, factor * fQ (n + h) :=
    Summable.tsum_le_tsum hterm hRsummable hscaledSummable
  have htailLe :
      ∑' n : ℕ, fQ (n + h) ≤ ∑' n : ℕ, fQ n := by
    have hsplit := hsum.sum_add_tsum_nat_add h
    have hprefixNonneg : 0 ≤ ∑ i ∈ Finset.range h, fQ i := by
      exact Finset.sum_nonneg (fun i _ => hQnonneg i)
    linarith
  calc
    Real.rpow (lambdaSq R s (.finite 1) a) (-1 / 2 : ℝ) = ∑' n : ℕ, fR n := by
      simpa [fR] using (multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum R s a hs)
    _ ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n := by
      exact mul_le_mul_of_nonneg_left htailLe hfactorNonneg
    _ = factor * Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
      simpa [fQ] using congrArg (fun x : ℝ => factor * x)
        (multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum Q s a hs).symm

/-- Depth-`j` form of the finite-`q = 1` lower ellipticity localization. -/
theorem multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.rpow (lambdaSq R s (.finite 1) a) (-1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
      ring
    simp [hdiff]
  simpa [htoNat] using
    (multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a s hs hRscale hsum)

theorem multiscale_ellipticity_lambdaSq_one_inv_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    (lambdaSq R s (.finite 1) a)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q s (.finite 1) a)⁻¹ := by
  have hhalf :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s hs hR hsum
  have hsqrt_nonneg :
      0 ≤ Real.rpow (lambdaSq R s (.finite 1) a) (-1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_lambdaSq_one_nonneg R s a hs) _
  have hsq := pow_le_pow_left₀ hsqrt_nonneg hhalf 2
  have hfactorSq :
      (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 =
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 =
          Real.rpow (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) ((s * (Int.toNat (Q.scale - k) : ℝ)) * 2) := by
        simpa using (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
          (s * (Int.toNat (Q.scale - k) : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) := by
        congr 1
        ring
  calc
    (lambdaSq R s (.finite 1) a)⁻¹ =
        (Real.rpow (lambdaSq R s (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
      symm
      exact sq_rpow_neg_half_eq_inv_of_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg R s a hs)
    _ ≤
        (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
          Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := hsq
    _ =
        (Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 *
          (lambdaSq Q s (.finite 1) a)⁻¹ := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_neg_half_eq_inv_of_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg Q s a hs)]
    _ = Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q s (.finite 1) a)⁻¹ := by
      rw [hfactorSq]

theorem multiscale_ellipticity_LambdaSq_one_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    finsetSsup (descendantsAtScale Q k) (fun R => LambdaSq R s (.finite 1) a) ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        LambdaSq Q s (.finite 1) a := by
  unfold finsetSsup
  have hne :
      ((fun R => LambdaSq R s (.finite 1) a) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨LambdaSq R s (.finite 1) a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact multiscale_ellipticity_LambdaSq_one_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s hs hR hsum

theorem multiscale_ellipticity_lambdaSq_one_inv_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s : ℝ)
    (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    finsetSsup (descendantsAtScale Q k) (fun R => (lambdaSq R s (.finite 1) a)⁻¹) ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q s (.finite 1) a)⁻¹ := by
  unfold finsetSsup
  have hne :
      ((fun R => (lambdaSq R s (.finite 1) a)⁻¹) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨(lambdaSq R s (.finite 1) a)⁻¹, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact multiscale_ellipticity_lambdaSq_one_inv_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s hs hR hsum

theorem thetaRatio_rpow_half_le_of_mem_descendantsAtScale {d : ℕ}
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
    Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  have hLambda :=
    multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s hs hR hBsum
  have hlambda :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a t ht hR hSigmaSum
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hLambdaQNonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs) _
  have hlambdaRNonneg :
      0 ≤ Real.rpow (lambdaSq R t (.finite 1) a) (-1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (multiscale_ellipticity_lambdaSq_one_nonneg R t a ht) _
  rw [thetaRatio_rpow_half_eq_mul_rpow_half_rpow_neg_half R s t a hs ht,
    thetaRatio_rpow_half_eq_mul_rpow_half_rpow_neg_half Q s t a hs ht]
  calc
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq R t (.finite 1) a) (-1 / 2 : ℝ) ≤
      (Real.rpow (3 : ℝ) (s * (h : ℝ)) * Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) *
        (Real.rpow (3 : ℝ) (t * (h : ℝ)) * Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) := by
      exact mul_le_mul hLambda hlambda hlambdaRNonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) hLambdaQNonneg)
    _ =
      Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) *
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) := by
      have hpow :
          Real.rpow (3 : ℝ) (s * (h : ℝ)) * Real.rpow (3 : ℝ) (t * (h : ℝ)) =
            Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) := by
        calc
          Real.rpow (3 : ℝ) (s * (h : ℝ)) * Real.rpow (3 : ℝ) (t * (h : ℝ)) =
              Real.rpow (3 : ℝ) (s * (h : ℝ) + t * (h : ℝ)) := by
            simpa using (Real.rpow_add h3 (s * (h : ℝ)) (t * (h : ℝ))).symm
          _ = Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) := by
            congr 1
            ring
      calc
        (Real.rpow (3 : ℝ) (s * (h : ℝ)) * Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) *
            (Real.rpow (3 : ℝ) (t * (h : ℝ)) * Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) =
          (Real.rpow (3 : ℝ) (s * (h : ℝ)) * Real.rpow (3 : ℝ) (t * (h : ℝ))) *
            (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
              Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) := by
          ring
        _ =
          Real.rpow (3 : ℝ) ((s + t) * (h : ℝ)) *
            (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
              Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) := by
          rw [hpow]

/-- Depth-`j` form of the `ThetaRatio` square-root localization. -/
theorem thetaRatio_rpow_half_le_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : R ∈ descendantsAtDepth Q j)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) ((s + t) * (j : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
      ring
    simp [hdiff]
  simpa [htoNat] using
    (thetaRatio_rpow_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a s t hs ht hRscale hBsum hSigmaSum)

theorem thetaRatio_le_of_mem_descendantsAtScale {d : ℕ}
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
    ThetaRatio R s t a ≤
      Real.rpow (3 : ℝ) (2 * (s + t) * (Int.toNat (Q.scale - k) : ℝ)) *
        ThetaRatio Q s t a := by
  have hhalf :=
    thetaRatio_rpow_half_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s t hs ht hR hBsum hSigmaSum
  have hsqrt_nonneg :
      0 ≤ Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) := by
    exact Real.rpow_nonneg (thetaRatio_nonneg R s t a hs ht) _
  have hsq := pow_le_pow_left₀ hsqrt_nonneg hhalf 2
  have hfactorSq :
      (Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 =
        Real.rpow (3 : ℝ) (2 * (s + t) * (Int.toNat (Q.scale - k) : ℝ)) := by
    calc
      (Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 =
          Real.rpow
            (Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ))) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (3 : ℝ) (((s + t) * (Int.toNat (Q.scale - k) : ℝ)) * 2) := by
        simpa using (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
          ((s + t) * (Int.toNat (Q.scale - k) : ℝ)) (2 : ℝ)).symm
      _ = Real.rpow (3 : ℝ) (2 * (s + t) * (Int.toNat (Q.scale - k) : ℝ)) := by
        congr 1
        ring
  calc
    ThetaRatio R s t a = (Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ)) ^ 2 := by
      symm
      exact sq_rpow_half_eq_self_of_nonneg (thetaRatio_nonneg R s t a hs ht)
    _ ≤
        (Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ)) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) ^ 2 := hsq
    _ =
        (Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ))) ^ 2 *
          ThetaRatio Q s t a := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_half_eq_self_of_nonneg (thetaRatio_nonneg Q s t a hs ht)]
    _ = Real.rpow (3 : ℝ) (2 * (s + t) * (Int.toNat (Q.scale - k) : ℝ)) *
          ThetaRatio Q s t a := by
      rw [hfactorSq]

theorem thetaRatio_rpow_half_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    finsetSsup (descendantsAtScale Q k)
        (fun R => Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ)) ≤
      Real.rpow (3 : ℝ) ((s + t) * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
  unfold finsetSsup
  have hne :
      ((fun R => Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ)) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ), ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact thetaRatio_rpow_half_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s t hs ht hR hBsum hSigmaSum

theorem thetaRatio_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    finsetSsup (descendantsAtScale Q k) (fun R => ThetaRatio R s t a) ≤
      Real.rpow (3 : ℝ) (2 * (s + t) * (Int.toNat (Q.scale - k) : ℝ)) *
        ThetaRatio Q s t a := by
  unfold finsetSsup
  have hne :
      ((fun R => ThetaRatio R s t a) '' (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨ThetaRatio R s t a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact thetaRatio_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s t hs ht hR hBsum hSigmaSum


end

end Homogenization
