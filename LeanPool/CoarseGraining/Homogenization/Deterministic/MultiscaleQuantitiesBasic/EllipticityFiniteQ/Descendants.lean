/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.EllipticityFiniteQ.ChangeOfQ

/-! # Descendants -/

namespace Homogenization

noncomputable section

theorem multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    Real.rpow (LambdaSq R s (.finite q) a) (q / 2) ≤
      Real.rpow (3 : ℝ) (s * q * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (q / 2)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs hq.le)) ?_
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
        Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (q / 2) ≤
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
            (q / 2) := by
      refine Real.rpow_le_rpow
        (maxDescendantBBlockNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      positivity
    calc
      fR n =
          factor *
            (geometricWeight s q (n + h) *
              Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (q / 2)) := by
        dsimp [fR, factor]
        rw [geometricWeight_shift (s := s) (q := q) h n]
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s q (n + h) *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
              (q / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (geometricWeight_nonneg (n + h) (mul_nonneg hs hq.le))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs hq.le)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
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
    Real.rpow (LambdaSq R s (.finite q) a) (q / 2) = ∑' n : ℕ, fR n := by
      simpa [fR] using
        (multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum R s q a hq
          (mul_nonneg hs hq.le))
    _ ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n := by
      exact mul_le_mul_of_nonneg_left htailLe hfactorNonneg
    _ = factor * Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
      simpa [fQ] using congrArg (fun x : ℝ => factor * x)
        (multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum Q s q a hq
          (mul_nonneg hs hq.le)).symm

theorem multiscale_ellipticity_LambdaSq_finite_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    LambdaSq R s (.finite q) a ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        LambdaSq Q s (.finite q) a := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hbase :=
    multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s q hs hq hR hsum
  have hfactorEq :
      Real.rpow factor (2 / q) =
        Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by
    dsimp [factor]
    have hmul : (s * q * (h : ℝ)) * (2 / q) = 2 * s * (h : ℝ) := by
      field_simp [hq.ne']
    calc
      Real.rpow (Real.rpow (3 : ℝ) (s * q * (h : ℝ))) (2 / q) =
          Real.rpow (3 : ℝ) ((s * q * (h : ℝ)) * (2 / q)) := by
            exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (s * q * (h : ℝ)) (2 / q)).symm
      _ = Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by simp [hmul]
  calc
    LambdaSq R s (.finite q) a ≤ Real.rpow factor (2 / q) * LambdaSq Q s (.finite q) a := by
      exact le_rpow_factor_mul_of_rpow_q_div_two_le hq
        (multiscale_ellipticity_LambdaSq_finite_nonneg R s q a hq.le (mul_nonneg hs hq.le))
        (multiscale_ellipticity_LambdaSq_finite_nonneg Q s q a hq.le (mul_nonneg hs hq.le))
        hfactorNonneg hbase
    _ = Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q s (.finite q) a := by
      rw [hfactorEq]

/-- A summable upper-ellipticity finite-`q` series remains summable after
restricting the base cube to a descendant. -/
theorem summable_geometricWeight_maxDescendantBBlockNormAtScale_rpow_q_div_two_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    Summable (fun n : ℕ =>
      geometricWeight s q n *
        Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
          (q / 2)) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a) (q / 2)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
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
            (q / 2) ≤
          Real.rpow
            (maxDescendantBBlockNormAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2) := by
      refine Real.rpow_le_rpow
        (maxDescendantBBlockNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      positivity
    calc
      fR n =
          factor *
            (geometricWeight s q (n + h) *
              Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
                (q / 2)) := by
        dsimp [fR, factor]
        rw [geometricWeight_shift (s := s) (q := q) h n]
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s q (n + h) *
            Real.rpow
              (maxDescendantBBlockNormAtScale Q
                (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (geometricWeight_nonneg (n + h) (mul_nonneg hs hq.le))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs hq.le)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  exact Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable

theorem multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    Real.rpow (lambdaSq R s (.finite q) a) (-q / 2) ≤
      Real.rpow (3 : ℝ) (s * q * (Int.toNat (Q.scale - k) : ℝ)) *
        Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a) (q / 2)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs hq.le)) ?_
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
        Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a) (q / 2) ≤
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
            (q / 2) := by
      refine Real.rpow_le_rpow
        (maxDescendantSigmaStarInvNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      positivity
    calc
      fR n =
          factor *
            (geometricWeight s q (n + h) *
              Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
                (q / 2)) := by
        dsimp [fR, factor]
        rw [geometricWeight_shift (s := s) (q := q) h n]
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s q (n + h) *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a)
              (q / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (geometricWeight_nonneg (n + h) (mul_nonneg hs hq.le))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs hq.le)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
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
    Real.rpow (lambdaSq R s (.finite q) a) (-q / 2) = ∑' n : ℕ, fR n := by
      simpa [fR] using
        (multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum R s q a hq
          (mul_nonneg hs hq.le))
    _ ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n := by
      exact mul_le_mul_of_nonneg_left htailLe hfactorNonneg
    _ = factor * Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
      simpa [fQ] using congrArg (fun x : ℝ => factor * x)
        (multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum Q s q a hq
          (mul_nonneg hs hq.le)).symm

theorem summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    Summable (fun n : ℕ =>
      geometricWeight s q n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
          (q / 2)) := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a) (q / 2)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
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
        maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a ≤
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a := by
      have hl : R.scale - (n : ℤ) ≤ R.scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (maxDescendantSigmaStarInvNormAtScale_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a hR hl)
    have hrpow :
        Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
            (q / 2) ≤
          Real.rpow
            (maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2) := by
      refine Real.rpow_le_rpow
        (maxDescendantSigmaStarInvNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      positivity
    calc
      fR n =
          factor *
            (geometricWeight s q (n + h) *
              Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
                (q / 2)) := by
        dsimp [fR, factor]
        rw [geometricWeight_shift (s := s) (q := q) h n]
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s q (n + h) *
            Real.rpow
              (maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (geometricWeight_nonneg (n + h) (mul_nonneg hs hq.le))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs hq.le)) ?_
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  exact Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable

theorem multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    (lambdaSq R s (.finite q) a)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q s (.finite q) a)⁻¹ := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hbase :=
    multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a s q hs hq hR hsum
  have hbase' :
      Real.rpow ((lambdaSq R s (.finite q) a)⁻¹) (q / 2) ≤
        factor * Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
    have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
    calc
      Real.rpow ((lambdaSq R s (.finite q) a)⁻¹) (q / 2) =
          Real.rpow (lambdaSq R s (.finite q) a) (-q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq R s (.finite q) a) (q / 2)).symm
      _ ≤ factor * Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := hbase
      _ = factor * Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
            simpa [hneg] using congrArg (fun x : ℝ => factor * x)
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2))
  have hfactorEq :
      Real.rpow factor (2 / q) =
        Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by
    dsimp [factor]
    have hmul : (s * q * (h : ℝ)) * (2 / q) = 2 * s * (h : ℝ) := by
      field_simp [hq.ne']
    calc
      Real.rpow (Real.rpow (3 : ℝ) (s * q * (h : ℝ))) (2 / q) =
          Real.rpow (3 : ℝ) ((s * q * (h : ℝ)) * (2 / q)) := by
            exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (s * q * (h : ℝ)) (2 / q)).symm
      _ = Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by simp [hmul]
  calc
    (lambdaSq R s (.finite q) a)⁻¹ ≤
        Real.rpow factor (2 / q) * (lambdaSq Q s (.finite q) a)⁻¹ := by
      exact le_rpow_factor_mul_of_rpow_q_div_two_le hq
        (inv_nonneg.mpr (multiscale_ellipticity_lambdaSq_finite_nonneg R s q a hq.le
          (mul_nonneg hs hq.le)))
        (inv_nonneg.mpr (multiscale_ellipticity_lambdaSq_finite_nonneg Q s q a hq.le
          (mul_nonneg hs hq.le)))
        hfactorNonneg hbase'
    _ = Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q s (.finite q) a)⁻¹ := by
      rw [hfactorEq]

theorem multiscale_ellipticity_LambdaSq_finite_le_of_mem_descendantsAtScale_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s) (hR : R ∈ descendantsAtScale Q k)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    LambdaSq R s (.finite q) a ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        LambdaSq Q t (.finite q) a := by
  have hs : 0 < s := lt_trans ht hts
  have hBnonneg :
      ∀ n : ℕ,
        0 ≤ Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
    intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)) :=
    summable_geometricWeight_of_lt hBnonneg hq ht hts hsum_t
  calc
    LambdaSq R s (.finite q) a ≤
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q s (.finite q) a := by
          exact multiscale_ellipticity_LambdaSq_finite_le_of_mem_descendantsAtScale
            (Q := Q) (R := R) (k := k) a s q hs.le hq hR hsum_s
    _ ≤ Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q t (.finite q) a := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact multiscale_ellipticity_LambdaSq_finite_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
              Q a hq ht hts hEll hData hsum_t
          · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s) (hR : R ∈ descendantsAtScale Q k)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    (lambdaSq R s (.finite q) a)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q t (.finite q) a)⁻¹ := by
  have hs : 0 < s := lt_trans ht hts
  have hSigmaNonneg :
      ∀ n : ℕ,
        0 ≤ Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2) := by
    intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) :=
    summable_geometricWeight_of_lt hSigmaNonneg hq ht hts hsum_t
  calc
    (lambdaSq R s (.finite q) a)⁻¹ ≤
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q s (.finite q) a)⁻¹ := by
          exact multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
            (Q := Q) (R := R) (k := k) a s q hs.le hq hR hsum_s
    _ ≤ Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q t (.finite q) a)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact multiscale_ellipticity_lambdaSq_finite_inv_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
              Q a hq ht hts hEll hData hsum_t
          · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _


end

end Homogenization
