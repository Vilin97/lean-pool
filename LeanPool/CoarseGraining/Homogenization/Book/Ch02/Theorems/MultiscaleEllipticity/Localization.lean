/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Infinity

/-! # Localization -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Localization for Chapter 2.5 Multiscale Ellipticity

This file proves descendant localization bounds and the unified finite/infinite
public order lemmas, including the theta-ratio controls.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

private theorem multiscaleDescendantWeight_nonneg {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (s : ℝ) :
    0 ≤ multiscaleDescendantWeight Q k s := by
  unfold multiscaleDescendantWeight
  exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem descendant_LambdaSq_infinity_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s : ℝ}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) :
    LambdaSq R s .infinity a ≤
      multiscaleDescendantWeight Q k s * LambdaSq Q s .infinity a := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  let h : ℕ := Int.toNat (Q.scale - k)
  have hh_int : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hW :
      multiscaleDescendantWeight Q k s =
        Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by
    unfold multiscaleDescendantWeight
    have hh_real : (((Q.scale - k : ℤ) : ℝ)) = (h : ℝ) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ)) hh_int.symm
    rw [hh_real]
  have hbddQ := LambdaSqInfinity_valueSet_bddAbove Q a hs.le
  have hneR :
      ({ M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantBMatrixNormAtScale R (R.scale - (n : ℤ)) a }).Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  change
    sSup
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantBMatrixNormAtScale R (R.scale - (n : ℤ)) a } ≤
      multiscaleDescendantWeight Q k s *
        sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a }
  refine csSup_le hneR ?_
  rintro M ⟨n, rfl⟩
  let l : ℤ := R.scale - (n : ℤ)
  have hl : l ≤ R.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hRscale : R.scale = k :=
    Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hscale :
      Q.scale - ((n + h : ℕ) : ℤ) = l := by
    dsimp [l]
    rw [hRscale]
    rw [hh_int]
    ring
  have hmaxle :
      maxDescendantBMatrixNormAtScale R l a ≤
        maxDescendantBMatrixNormAtScale Q l a :=
    maxDescendantBMatrixNormAtScale_le_of_mem_descendantsAtScale a hR hl
  have htermle :
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantBMatrixNormAtScale R l a ≤
        Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantBMatrixNormAtScale Q l a :=
    mul_le_mul_of_nonneg_left hmaxle (infinityWeight_nonneg s n)
  have hmemQ :
      Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) *
          maxDescendantBMatrixNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a ∈
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } :=
    ⟨n + h, rfl⟩
  have hQle :
      Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) *
          maxDescendantBMatrixNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a ≤
        sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } :=
    le_csSup hbddQ hmemQ
  have hWnonneg : 0 ≤ multiscaleDescendantWeight Q k s :=
    multiscaleDescendantWeight_nonneg Q k s
  have hscaled :=
    mul_le_mul_of_nonneg_left hQle hWnonneg
  calc
    Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        maxDescendantBMatrixNormAtScale R l a ≤
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        maxDescendantBMatrixNormAtScale Q l a := htermle
    _ =
      multiscaleDescendantWeight Q k s *
        (Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) *
          maxDescendantBMatrixNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a) := by
        rw [hW, infinityWeight_shift s h n, hscale]
        ring
    _ ≤
      multiscaleDescendantWeight Q k s *
        sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := hscaled

theorem descendant_lambdaSq_infinity_inv_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s : ℝ}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) :
    (lambdaSq R s .infinity a)⁻¹ ≤
      multiscaleDescendantWeight Q k s * (lambdaSq Q s .infinity a)⁻¹ := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  let h : ℕ := Int.toNat (Q.scale - k)
  have hh_int : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hW :
      multiscaleDescendantWeight Q k s =
        Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by
    unfold multiscaleDescendantWeight
    have hh_real : (((Q.scale - k : ℤ) : ℝ)) = (h : ℝ) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ)) hh_int.symm
    rw [hh_real]
  have hbddQ := lambdaSqInfinity_denominator_valueSet_bddAbove Q a hs.le
  have hneR :
      ({ M : ℝ | ∃ n : ℕ,
          M =
            Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
              maxDescendantSigmaStarInvMatrixNormAtScale R (R.scale - (n : ℤ)) a }).Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  simp only [lambdaSq, lambdaSqInfinity, inv_inv]
  change
    (sSup
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale R (R.scale - (n : ℤ)) a }) ≤
      multiscaleDescendantWeight Q k s *
        (sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a })
  refine csSup_le hneR ?_
  rintro M ⟨n, rfl⟩
  let l : ℤ := R.scale - (n : ℤ)
  have hl : l ≤ R.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hRscale : R.scale = k :=
    Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  have hscale :
      Q.scale - ((n + h : ℕ) : ℤ) = l := by
    dsimp [l]
    rw [hRscale]
    rw [hh_int]
    ring
  have hmaxle :
      maxDescendantSigmaStarInvMatrixNormAtScale R l a ≤
        maxDescendantSigmaStarInvMatrixNormAtScale Q l a :=
    maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale a hR hl
  have htermle :
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale R l a ≤
        Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q l a :=
    mul_le_mul_of_nonneg_left hmaxle (infinityWeight_nonneg s n)
  have hmemQ :
      Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - ((n + h : ℕ) : ℤ)) a ∈
        { M : ℝ | ∃ n : ℕ,
            M =
              Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } :=
    ⟨n + h, rfl⟩
  have hQle :
      Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - ((n + h : ℕ) : ℤ)) a ≤
        sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } :=
    le_csSup hbddQ hmemQ
  have hWnonneg : 0 ≤ multiscaleDescendantWeight Q k s :=
    multiscaleDescendantWeight_nonneg Q k s
  have hscaled :=
    mul_le_mul_of_nonneg_left hQle hWnonneg
  calc
    Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        maxDescendantSigmaStarInvMatrixNormAtScale R l a ≤
      Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
        maxDescendantSigmaStarInvMatrixNormAtScale Q l a := htermle
    _ =
      multiscaleDescendantWeight Q k s *
        (Real.rpow (3 : ℝ) (-2 * s * ((n + h : ℕ) : ℝ)) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - ((n + h : ℕ) : ℤ)) a) := by
        rw [hW, infinityWeight_shift s h n, hscale]
        ring
    _ ≤
      multiscaleDescendantWeight Q k s *
        sSup
          { M : ℝ | ∃ n : ℕ,
              M =
                Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                  maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a } := hscaled

private theorem tsum_shift_le_mul_tsum_of_nonneg_le
    {fQ fR : ℕ → ℝ} {factor : ℝ} (h : ℕ)
    (hsum : Summable fQ)
    (hQnonneg : ∀ n : ℕ, 0 ≤ fQ n)
    (hRnonneg : ∀ n : ℕ, 0 ≤ fR n)
    (hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h))
    (hfactorNonneg : 0 ≤ factor) :
    (∑' n : ℕ, fR n) ≤ factor * ∑' n : ℕ, fQ n := by
  have htailSummable : Summable (fun n : ℕ => fQ (n + h)) :=
    (summable_nat_add_iff h).2 hsum
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
    have hprefixNonneg : 0 ≤ ∑ i ∈ Finset.range h, fQ i :=
      Finset.sum_nonneg (fun i _ => hQnonneg i)
    linarith
  calc
    (∑' n : ℕ, fR n) ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n :=
      mul_le_mul_of_nonneg_left htailLe hfactorNonneg

private theorem rpow_geometric_shift_factor_two_div
    {s q : ℝ} (h : ℕ) (hqpos : 0 < q) :
    Real.rpow (Real.rpow (3 : ℝ) (s * q * (h : ℝ))) (2 / q) =
      Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by
  have hmul : (s * q * (h : ℝ)) * (2 / q) = 2 * s * (h : ℝ) := by
    field_simp [hqpos.ne']
  calc
    Real.rpow (Real.rpow (3 : ℝ) (s * q * (h : ℝ))) (2 / q) =
        Real.rpow (3 : ℝ) ((s * q * (h : ℝ)) * (2 / q)) := by
          exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
            (s * q * (h : ℝ)) (2 / q)).symm
    _ = Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by simp [hmul]

theorem descendant_LambdaSq_finite_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s q : ℝ}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (hq : 1 ≤ q) :
    LambdaSq R s (.finite q) a ≤
      multiscaleDescendantWeight Q k s * LambdaSq Q s (.finite q) a := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  let h : ℕ := Int.toNat (Q.scale - k)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k :=
    Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow (maxDescendantBMatrixNormAtScale R (R.scale - (n : ℤ)) a) (q / 2)
  have hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow
            (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) := by
    exact summable_B_series_pointwiseCoeffField Q a hs hqpos
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hqpos.le)
    · refine Real.rpow_nonneg ?_ _
      exact maxDescendantBMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hmax :
        maxDescendantBMatrixNormAtScale R (R.scale - (n : ℤ)) a ≤
          maxDescendantBMatrixNormAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) a := by
      have hl : R.scale - (n : ℤ) ≤ R.scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (maxDescendantBMatrixNormAtScale_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a hR hl)
    have hrpow :
        Real.rpow (maxDescendantBMatrixNormAtScale R (R.scale - (n : ℤ)) a)
            (q / 2) ≤
          Real.rpow
            (maxDescendantBMatrixNormAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2) := by
      refine Real.rpow_le_rpow
        (maxDescendantBMatrixNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      positivity
    have hweight :
        geometricWeight s q n = factor * geometricWeight s q (n + h) := by
      simpa [factor, geometricWeight_eq_old] using
        Homogenization.geometricWeight_shift (s := s) (q := q) h n
    calc
      fR n =
          factor *
            (geometricWeight s q (n + h) *
              Real.rpow (maxDescendantBMatrixNormAtScale R (R.scale - (n : ℤ)) a)
                (q / 2)) := by
        dsimp [fR]
        rw [hweight]
        ring
      _ ≤ factor *
          (geometricWeight s q (n + h) *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q
                (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (by
            simpa [geometricWeight_eq_old] using
              Homogenization.geometricWeight_nonneg (n + h) (mul_nonneg hs.le hqpos.le))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hqpos.le)
    · refine Real.rpow_nonneg ?_ _
      exact maxDescendantBMatrixNormAtScale_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hbase :
      Real.rpow (LambdaSq R s (.finite q) a) (q / 2) ≤
        factor * Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
    calc
      Real.rpow (LambdaSq R s (.finite q) a) (q / 2) =
          ∑' n : ℕ, fR n := by
        simpa [fR] using
          LambdaSqFinite_rpow_q_div_two_eq_tsum R s q a hqpos
            (mul_nonneg hs.le hqpos.le)
      _ ≤ factor * ∑' n : ℕ, fQ n :=
        tsum_shift_le_mul_tsum_of_nonneg_le h
          (by simpa [fQ] using hsum) hQnonneg hRnonneg hterm hfactorNonneg
      _ = factor * Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
        simpa [fQ] using congrArg (fun x : ℝ => factor * x)
          (LambdaSqFinite_rpow_q_div_two_eq_tsum Q s q a hqpos
            (mul_nonneg hs.le hqpos.le)).symm
  have hfactorEq :
      Real.rpow factor (2 / q) =
        Real.rpow (3 : ℝ) (2 * s * (h : ℝ)) := by
    simpa [factor] using rpow_geometric_shift_factor_two_div h hqpos
  calc
    LambdaSq R s (.finite q) a ≤
        Real.rpow factor (2 / q) * LambdaSq Q s (.finite q) a := by
      exact Homogenization.le_rpow_factor_mul_of_rpow_q_div_two_le hqpos
        (LambdaSq_finite_nonneg R a hs hq)
        (LambdaSq_finite_nonneg Q a hs hq)
        hfactorNonneg hbase
    _ = multiscaleDescendantWeight Q k s * LambdaSq Q s (.finite q) a := by
      rw [hfactorEq, old_descendantWeight_eq_multiscaleDescendantWeight Q hk s]

theorem descendant_lambdaSq_finite_inv_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s q : ℝ}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (hq : 1 ≤ q) :
    (lambdaSq R s (.finite q) a)⁻¹ ≤
      multiscaleDescendantWeight Q k s * (lambdaSq Q s (.finite q) a)⁻¹ := by
  have hk : k ≤ Q.scale := Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  let h : ℕ := Int.toNat (Q.scale - k)
  let factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ))
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k :=
    Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
        (q / 2)
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s q n *
      Real.rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale R (R.scale - (n : ℤ)) a)
        (q / 2)
  have hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) := by
    exact summable_sigmaStarInv_series_pointwiseCoeffField Q a hs hqpos
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hqpos.le)
    · refine Real.rpow_nonneg ?_ _
      exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hmax :
        maxDescendantSigmaStarInvMatrixNormAtScale R (R.scale - (n : ℤ)) a ≤
          maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - ((n + h : ℕ) : ℤ)) a := by
      have hl : R.scale - (n : ℤ) ≤ R.scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a hR hl)
    have hrpow :
        Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale R (R.scale - (n : ℤ)) a)
            (q / 2) ≤
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2) := by
      refine Real.rpow_le_rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg R
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
        hmax ?_
      positivity
    have hweight :
        geometricWeight s q n = factor * geometricWeight s q (n + h) := by
      simpa [factor, geometricWeight_eq_old] using
        Homogenization.geometricWeight_shift (s := s) (q := q) h n
    calc
      fR n =
          factor *
            (geometricWeight s q (n + h) *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale R
                  (R.scale - (n : ℤ)) a) (q / 2)) := by
        dsimp [fR]
        rw [hweight]
        ring
      _ ≤ factor *
          (geometricWeight s q (n + h) *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - ((n + h : ℕ) : ℤ)) a) (q / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hrpow
          (by
            simpa [geometricWeight_eq_old] using
              Homogenization.geometricWeight_nonneg (n + h) (mul_nonneg hs.le hqpos.le))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hqpos.le)
    · refine Real.rpow_nonneg ?_ _
      exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hbase :
      Real.rpow (lambdaSq R s (.finite q) a) (-q / 2) ≤
        factor * Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
    calc
      Real.rpow (lambdaSq R s (.finite q) a) (-q / 2) =
          ∑' n : ℕ, fR n := by
        simpa [fR] using
          lambdaSqFinite_rpow_neg_q_div_two_eq_tsum R s q a hqpos
            (mul_nonneg hs.le hqpos.le)
      _ ≤ factor * ∑' n : ℕ, fQ n :=
        tsum_shift_le_mul_tsum_of_nonneg_le h
          (by simpa [fQ] using hsum) hQnonneg hRnonneg hterm hfactorNonneg
      _ = factor * Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
        simpa [fQ] using congrArg (fun x : ℝ => factor * x)
          (lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s q a hqpos
            (mul_nonneg hs.le hqpos.le)).symm
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
    simpa [factor] using rpow_geometric_shift_factor_two_div h hqpos
  calc
    (lambdaSq R s (.finite q) a)⁻¹ ≤
        Real.rpow factor (2 / q) * (lambdaSq Q s (.finite q) a)⁻¹ := by
      exact Homogenization.le_rpow_factor_mul_of_rpow_q_div_two_le hqpos
        (inv_nonneg.mpr (lambdaSq_finite_nonneg R a hs hq))
        (inv_nonneg.mpr (lambdaSq_finite_nonneg Q a hs hq))
        hfactorNonneg hbase'
    _ = multiscaleDescendantWeight Q k s * (lambdaSq Q s (.finite q) a)⁻¹ := by
      rw [hfactorEq, old_descendantWeight_eq_multiscaleDescendantWeight Q hk s]

theorem maxDescendant_b_le_maxDescendant_LambdaSq_finite {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s q : ℝ}
    (hk : k ≤ Q.scale) (hs : 0 < s) (hq : 1 ≤ q) :
    maxDescendantBMatrixNormAtScale Q k a ≤
      maxDescendantUpperEllipticityAtScale Q k s (.finite q) a := by
  unfold maxDescendantBMatrixNormAtScale maxDescendantUpperEllipticityAtScale
  exact finsetSupReal_mono (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) fun R _ =>
      oneCube_b_le_LambdaSq_finite R a hs hq

theorem maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_finite_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {k : ℤ} {s q : ℝ} (hk : k ≤ Q.scale) (hs : 0 < s) (hq : 1 ≤ q) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      maxDescendantLowerEllipticityInvAtScale Q k s (.finite q) a := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale maxDescendantLowerEllipticityInvAtScale
  exact finsetSupReal_mono (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) fun R _ =>
      oneCube_sigmaStarInv_le_lambdaSq_finite_inv R a hs hq

theorem maxDescendant_LambdaSq_finite_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s q : ℝ}
    (hk : k ≤ Q.scale) (hs : 0 < s) (hq : 1 ≤ q) :
    maxDescendantUpperEllipticityAtScale Q k s (.finite q) a ≤
      multiscaleDescendantWeight Q k s * LambdaSq Q s (.finite q) a := by
  unfold maxDescendantUpperEllipticityAtScale finsetSupReal
  have hne :
      ((fun R => LambdaSq R s (.finite q) a) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨LambdaSq R s (.finite q) a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact descendant_LambdaSq_finite_le (Q := Q) (R := R) (k := k) a hR hs hq

theorem maxDescendant_lambdaSq_finite_inv_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s q : ℝ}
    (hk : k ≤ Q.scale) (hs : 0 < s) (hq : 1 ≤ q) :
    maxDescendantLowerEllipticityInvAtScale Q k s (.finite q) a ≤
      multiscaleDescendantWeight Q k s * (lambdaSq Q s (.finite q) a)⁻¹ := by
  unfold maxDescendantLowerEllipticityInvAtScale finsetSupReal
  have hne :
      ((fun R => (lambdaSq R s (.finite q) a)⁻¹) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨(lambdaSq R s (.finite q) a)⁻¹, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact descendant_lambdaSq_finite_inv_le (Q := Q) (R := R) (k := k) a hR hs hq

theorem maxDescendant_b_le_maxDescendant_LambdaSq_infinity {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s : ℝ}
    (hk : k ≤ Q.scale) (hs : 0 < s) :
    maxDescendantBMatrixNormAtScale Q k a ≤
      maxDescendantUpperEllipticityAtScale Q k s .infinity a := by
  unfold maxDescendantBMatrixNormAtScale maxDescendantUpperEllipticityAtScale
  exact finsetSupReal_mono (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) fun R _ =>
      oneCube_b_le_LambdaSq_infinity R a hs

theorem maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_infinity_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {k : ℤ} {s : ℝ} (hk : k ≤ Q.scale) (hs : 0 < s) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      maxDescendantLowerEllipticityInvAtScale Q k s .infinity a := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale
    maxDescendantLowerEllipticityInvAtScale
  exact finsetSupReal_mono (descendantsAtScale Q k)
    (descendantsAtScale_nonempty Q hk) fun R _ =>
      oneCube_sigmaStarInv_le_lambdaSq_infinity_inv R a hs

theorem maxDescendant_LambdaSq_infinity_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s : ℝ}
    (hk : k ≤ Q.scale) (hs : 0 < s) :
    maxDescendantUpperEllipticityAtScale Q k s .infinity a ≤
      multiscaleDescendantWeight Q k s * LambdaSq Q s .infinity a := by
  unfold maxDescendantUpperEllipticityAtScale finsetSupReal
  have hne :
      ((fun R => LambdaSq R s .infinity a) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨LambdaSq R s .infinity a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact descendant_LambdaSq_infinity_le (Q := Q) (R := R) (k := k) a hR hs

theorem maxDescendant_lambdaSq_infinity_inv_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s : ℝ}
    (hk : k ≤ Q.scale) (hs : 0 < s) :
    maxDescendantLowerEllipticityInvAtScale Q k s .infinity a ≤
      multiscaleDescendantWeight Q k s * (lambdaSq Q s .infinity a)⁻¹ := by
  unfold maxDescendantLowerEllipticityInvAtScale finsetSupReal
  have hne :
      ((fun R => (lambdaSq R s .infinity a)⁻¹) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨(lambdaSq R s .infinity a)⁻¹, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact descendant_lambdaSq_infinity_inv_le (Q := Q) (R := R) (k := k) a hR hs

theorem LambdaSq_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    0 ≤ LambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact LambdaSq_finite_nonneg Q a hs (by simpa using hq)
  | infinity =>
      exact LambdaSq_infinity_nonneg Q a hs

theorem lambdaSq_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    0 ≤ lambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact lambdaSq_finite_nonneg Q a hs (by simpa using hq)
  | infinity =>
      exact lambdaSq_infinity_nonneg Q a hs

theorem LambdaSq_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    0 < LambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact LambdaSq_finite_pos Q a hs (by simpa using hq)
  | infinity =>
      exact LambdaSq_infinity_pos Q a hs

theorem lambdaSq_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    0 < lambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact lambdaSq_finite_pos Q a hs (by simpa using hq)
  | infinity =>
      exact lambdaSq_infinity_pos Q a hs

theorem lambdaSq_mono {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s : ℝ}
    {q : MultiscaleExponent} (ht : 0 < t) (hts : t < s)
    (hq : q.IsAdmissible) :
    lambdaSq Q t q a ≤ lambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact lambdaSq_finite_mono Q a ht hts (by simpa using hq)
  | infinity =>
      exact lambdaSq_infinity_mono Q a ht hts

theorem LambdaSq_antitone {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s : ℝ}
    {q : MultiscaleExponent} (ht : 0 < t) (hts : t < s)
    (hq : q.IsAdmissible) :
    LambdaSq Q s q a ≤ LambdaSq Q t q a := by
  cases q with
  | finite q =>
      exact LambdaSq_finite_antitone Q a ht hts (by simpa using hq)
  | infinity =>
      exact LambdaSq_infinity_antitone Q a ht hts

theorem lambdaSq_le_oneCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    lambdaSq Q s q a ≤ (coarseSigmaStarInvMatrixNorm Q a)⁻¹ := by
  cases q with
  | finite q =>
      exact lambdaSq_finite_le_oneCube Q a hs (by simpa using hq)
  | infinity =>
      exact lambdaSq_infinity_le_oneCube Q a hs

theorem oneCube_b_le_LambdaSq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    coarseBMatrixNorm Q a ≤ LambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact oneCube_b_le_LambdaSq_finite Q a hs (by simpa using hq)
  | infinity =>
      exact oneCube_b_le_LambdaSq_infinity Q a hs

theorem maxDescendant_b_le_maxDescendant_LambdaSq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s : ℝ}
    {q : MultiscaleExponent} (hk : k ≤ Q.scale) (hs : 0 < s)
    (hq : q.IsAdmissible) :
    maxDescendantBMatrixNormAtScale Q k a ≤
      maxDescendantUpperEllipticityAtScale Q k s q a := by
  cases q with
  | finite q =>
      exact maxDescendant_b_le_maxDescendant_LambdaSq_finite Q a hk hs
        (by simpa using hq)
  | infinity =>
      exact maxDescendant_b_le_maxDescendant_LambdaSq_infinity Q a hk hs

theorem maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {k : ℤ} {s : ℝ} {q : MultiscaleExponent}
    (hk : k ≤ Q.scale) (hs : 0 < s) (hq : q.IsAdmissible) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      maxDescendantLowerEllipticityInvAtScale Q k s q a := by
  cases q with
  | finite q =>
      exact maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_finite_inv Q a hk hs
        (by simpa using hq)
  | infinity =>
      exact maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_infinity_inv Q a hk hs

theorem maxDescendant_LambdaSq_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s : ℝ}
    {q : MultiscaleExponent} (hk : k ≤ Q.scale) (hs : 0 < s)
    (hq : q.IsAdmissible) :
    maxDescendantUpperEllipticityAtScale Q k s q a ≤
      multiscaleDescendantWeight Q k s * LambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact maxDescendant_LambdaSq_finite_le Q a hk hs (by simpa using hq)
  | infinity =>
      exact maxDescendant_LambdaSq_infinity_le Q a hk hs

theorem maxDescendant_lambdaSq_inv_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {k : ℤ} {s : ℝ}
    {q : MultiscaleExponent} (hk : k ≤ Q.scale) (hs : 0 < s)
    (hq : q.IsAdmissible) :
    maxDescendantLowerEllipticityInvAtScale Q k s q a ≤
      multiscaleDescendantWeight Q k s * (lambdaSq Q s q a)⁻¹ := by
  cases q with
  | finite q =>
      exact maxDescendant_lambdaSq_finite_inv_le Q a hk hs (by simpa using hq)
  | infinity =>
      exact maxDescendant_lambdaSq_infinity_inv_le Q a hk hs

theorem descendant_LambdaSq_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (hq : q.IsAdmissible) :
    LambdaSq R s q a ≤
      multiscaleDescendantWeight Q k s * LambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact descendant_LambdaSq_finite_le (Q := Q) (R := R) (k := k) a hR hs
        (by simpa using hq)
  | infinity =>
      exact descendant_LambdaSq_infinity_le (Q := Q) (R := R) (k := k) a hR hs

theorem descendant_lambdaSq_inv_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s : ℝ}
    {q : MultiscaleExponent}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (hq : q.IsAdmissible) :
    (lambdaSq R s q a)⁻¹ ≤
      multiscaleDescendantWeight Q k s * (lambdaSq Q s q a)⁻¹ := by
  cases q with
  | finite q =>
      exact descendant_lambdaSq_finite_inv_le (Q := Q) (R := R) (k := k) a hR hs
        (by simpa using hq)
  | infinity =>
      exact descendant_lambdaSq_infinity_inv_le (Q := Q) (R := R) (k := k) a hR hs

theorem ThetaRatio_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    0 ≤ ThetaRatio Q s t a := by
  rw [ThetaRatio, LambdaS, lambdaS, div_eq_mul_inv]
  exact mul_nonneg
    (LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1))
    (inv_nonneg.mpr (lambdaSq_finite_nonneg Q a ht (by norm_num : (1 : ℝ) ≤ 1)))

theorem one_le_ThetaRatio_of_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    1 ≤ ThetaRatio Q s t a := by
  have hq : (MultiscaleExponent.finite (1 : ℝ)).IsAdmissible := by
    norm_num
  have hchain :
      lambdaSq Q t (.finite 1) a ≤ LambdaSq Q s (.finite 1) a := by
    calc
      lambdaSq Q t (.finite 1) a ≤
          (coarseSigmaStarInvMatrixNorm Q a)⁻¹ :=
            lambdaSq_le_oneCube Q a ht hq
      _ ≤ coarseBMatrixNorm Q a := oneCube_sigmaStarInv_le_b Q a
      _ ≤ LambdaSq Q s (.finite 1) a := oneCube_b_le_LambdaSq Q a hs hq
  have hlambda_pos :
      0 < lambdaSq Q t (.finite 1) a :=
    lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  rw [ThetaRatio, LambdaS, lambdaS]
  exact (one_le_div hlambda_pos).mpr hchain

theorem one_le_ThetaRatio {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s t : ℝ}
    (ht : 0 < t) (hts : t < s) :
    1 ≤ ThetaRatio Q s t a :=
  one_le_ThetaRatio_of_pos Q a (lt_trans ht hts) ht

theorem descendant_ThetaRatio_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s t : ℝ}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (ht : 0 < t) :
    ThetaRatio R s t a ≤
      (multiscaleDescendantWeight Q k s *
          multiscaleDescendantWeight Q k t) *
        ThetaRatio Q s t a := by
  let Ws : ℝ := multiscaleDescendantWeight Q k s
  let Wt : ℝ := multiscaleDescendantWeight Q k t
  have hLambda :
      LambdaSq R s (.finite 1) a ≤ Ws * LambdaSq Q s (.finite 1) a := by
    simpa [Ws] using
      descendant_LambdaSq_finite_le (Q := Q) (R := R) (k := k) a hR hs
        (by norm_num : (1 : ℝ) ≤ 1)
  have hlambda :
      (lambdaSq R t (.finite 1) a)⁻¹ ≤ Wt * (lambdaSq Q t (.finite 1) a)⁻¹ := by
    simpa [Wt] using
      descendant_lambdaSq_finite_inv_le (Q := Q) (R := R) (k := k) a hR ht
        (by norm_num : (1 : ℝ) ≤ 1)
  have hInvR_nonneg : 0 ≤ (lambdaSq R t (.finite 1) a)⁻¹ :=
    inv_nonneg.mpr (lambdaSq_finite_nonneg R a ht (by norm_num : (1 : ℝ) ≤ 1))
  have hWs_nonneg : 0 ≤ Ws := by
    dsimp [Ws, multiscaleDescendantWeight]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hLambdaQ_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1)
  have hWsLambda_nonneg : 0 ≤ Ws * LambdaSq Q s (.finite 1) a :=
    mul_nonneg hWs_nonneg hLambdaQ_nonneg
  calc
    ThetaRatio R s t a =
        LambdaSq R s (.finite 1) a * (lambdaSq R t (.finite 1) a)⁻¹ := by
          rw [ThetaRatio, LambdaS, lambdaS, div_eq_mul_inv]
    _ ≤ (Ws * LambdaSq Q s (.finite 1) a) *
          (Wt * (lambdaSq Q t (.finite 1) a)⁻¹) := by
          exact mul_le_mul hLambda hlambda hInvR_nonneg hWsLambda_nonneg
    _ =
        (multiscaleDescendantWeight Q k s * multiscaleDescendantWeight Q k t) *
          ThetaRatio Q s t a := by
          rw [ThetaRatio, LambdaS, lambdaS, div_eq_mul_inv]
          simp [Ws, Wt, mul_assoc, mul_left_comm, mul_comm]

theorem descendant_ThetaRatio_rpow_half_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) {s t : ℝ}
    (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s) (ht : 0 < t) :
    Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
      Real.rpow
        ((multiscaleDescendantWeight Q k s *
            multiscaleDescendantWeight Q k t) *
          ThetaRatio Q s t a)
        (1 / 2 : ℝ) := by
  exact Real.rpow_le_rpow (ThetaRatio_nonneg R a hs ht)
    (descendant_ThetaRatio_le (Q := Q) (R := R) (k := k) a hR hs ht)
    (by norm_num : 0 ≤ (1 / 2 : ℝ))

end

end Ch02
end Book
end Homogenization
