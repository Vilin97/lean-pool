/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.OneCubeBounds

/-! # Change Exponent Discount -/

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Finite-exponent multiscale ellipticity: discount change of exponent
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

private theorem book_geometricWeight_changeOfQ_tsum_le {H : ℕ → ℝ} {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hH_nonneg : ∀ n, 0 ≤ H n)
    (hsum_p :
      Summable (fun n : ℕ => geometricWeight s p n * Real.rpow (H n) (p / 2))) :
    ∑' n : ℕ, geometricWeight s q n * Real.rpow (H n) (q / 2) ≤
      geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
        Real.rpow
          (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
          (q / p) := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hq_div : 1 ≤ q / p := by
    field_simp [hp.ne']
    exact hpq
  let A : ℕ → ℝ := fun n =>
    Real.rpow (3 : ℝ) (-s * p * (n : ℝ)) * Real.rpow (H n) (p / 2)
  have hA_nonneg : ∀ n, 0 ≤ A n := by
    intro n
    dsimp [A]
    refine mul_nonneg ?_ ?_
    · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    · exact Real.rpow_nonneg (hH_nonneg n) _
  have hdisc_p_pos : 0 < geometricDiscount s p :=
    by
      simpa [geometricDiscount_eq_old] using
        Homogenization.geometricDiscount_pos (mul_pos hs hp)
  have hdisc_q_nonneg : 0 ≤ geometricDiscount s q :=
    by
      simpa [geometricDiscount_eq_old] using
        Homogenization.geometricDiscount_nonneg (mul_nonneg hs.le hq.le)
  have hAweighted :
      Summable (fun n : ℕ => geometricDiscount s p * A n) := by
    simpa [A, geometricWeight, mul_assoc, mul_left_comm, mul_comm] using hsum_p
  have hAsum : Summable A := (summable_mul_left_iff hdisc_p_pos.ne').1 hAweighted
  have hArpow_sum : Summable (fun n : ℕ => Real.rpow (A n) (q / p)) :=
    Homogenization.summable_rpow_of_nonneg_of_one_le hq_div hA_nonneg hAsum
  have hArpow_le :
      ∑' n : ℕ, Real.rpow (A n) (q / p) ≤ Real.rpow (∑' n : ℕ, A n) (q / p) :=
    Homogenization.tsum_rpow_le_rpow_tsum_of_nonneg hq_div hA_nonneg hAsum
  have hAq_rpow :
      ∀ n : ℕ,
        Real.rpow (A n) (q / p) =
          Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) * Real.rpow (H n) (q / 2) := by
    intro n
    have hmul1 : (-s * p * (n : ℝ)) * (q / p) = -s * q * (n : ℝ) := by
      field_simp [hp.ne']
    have hmul2 : (p / 2 : ℝ) * (q / p) = q / 2 := by
      field_simp [hp.ne']
    calc
      Real.rpow (A n) (q / p) =
          Real.rpow
              (Real.rpow (3 : ℝ) (-s * p * (n : ℝ)) * Real.rpow (H n) (p / 2))
              (q / p) := by
            rfl
      _ =
          Real.rpow (Real.rpow (3 : ℝ) (-s * p * (n : ℝ))) (q / p) *
            Real.rpow (Real.rpow (H n) (p / 2)) (q / p) := by
              exact Real.mul_rpow
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
                (Real.rpow_nonneg (hH_nonneg n) _)
      _ =
          Real.rpow (3 : ℝ) ((-s * p * (n : ℝ)) * (q / p)) *
            Real.rpow (H n) ((p / 2) * (q / p)) := by
              congr 1
              · symm
                exact Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
                  (-s * p * (n : ℝ)) (q / p)
              · symm
                exact Real.rpow_mul (hH_nonneg n) (p / 2) (q / p)
      _ =
          Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) * Real.rpow (H n) (q / 2) := by
            rw [hmul1, hmul2]
  have hSeries_q :
      ∑' n : ℕ, geometricWeight s q n * Real.rpow (H n) (q / 2) =
        geometricDiscount s q * ∑' n : ℕ, Real.rpow (A n) (q / p) := by
    calc
      ∑' n : ℕ, geometricWeight s q n * Real.rpow (H n) (q / 2) =
          ∑' n : ℕ, geometricDiscount s q * Real.rpow (A n) (q / p) := by
            apply tsum_congr
            intro n
            simpa [geometricWeight, mul_assoc, mul_left_comm, mul_comm] using
              congrArg (fun x : ℝ => geometricDiscount s q * x) (hAq_rpow n).symm
      _ = geometricDiscount s q * ∑' n : ℕ, Real.rpow (A n) (q / p) := by
            simpa using (Summable.tsum_mul_left (geometricDiscount s q) hArpow_sum)
  have hSeries_p :
      geometricDiscount s p * ∑' n : ℕ, A n =
        ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
    calc
      geometricDiscount s p * ∑' n : ℕ, A n =
          ∑' n : ℕ, geometricDiscount s p * A n := by
            symm
            simpa using (Summable.tsum_mul_left (geometricDiscount s p) hAsum)
      _ = ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
            apply tsum_congr
            intro n
            simp [A, geometricWeight, mul_assoc, mul_comm]
  have hSeries_p_nonneg :
      0 ≤ ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
    refine tsum_nonneg ?_
    intro n
    exact mul_nonneg
      (by
        simpa [geometricWeight_eq_old] using
          Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hp.le))
      (Real.rpow_nonneg (hH_nonneg n) _)
  have hAsum_eq :
      ∑' n : ℕ, A n =
        (geometricDiscount s p)⁻¹ *
          ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
    calc
      ∑' n : ℕ, A n =
          ((geometricDiscount s p)⁻¹ * geometricDiscount s p) *
            ∑' n : ℕ, A n := by
              rw [inv_mul_cancel₀ hdisc_p_pos.ne', one_mul]
      _ = (geometricDiscount s p)⁻¹ * (geometricDiscount s p * ∑' n : ℕ, A n) := by
            ring
      _ =
          (geometricDiscount s p)⁻¹ *
            ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
              rw [hSeries_p]
  have hAsum_rpow_eq :
      Real.rpow (∑' n : ℕ, A n) (q / p) =
        Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow
            (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
            (q / p) := by
    rw [hAsum_eq]
    calc
      Real.rpow
          ((geometricDiscount s p)⁻¹ *
            ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
          (q / p) =
          Real.rpow ((geometricDiscount s p)⁻¹) (q / p) *
            Real.rpow
              (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
              (q / p) := by
            exact Real.mul_rpow
              (inv_nonneg.mpr (by
                simpa [geometricDiscount_eq_old] using
                  Homogenization.geometricDiscount_nonneg (mul_nonneg hs.le hp.le)))
              hSeries_p_nonneg
      _ =
          Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow
              (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
              (q / p) := by
            have hnegdiv : -(q / p) = -q / p := by ring
            rw [show Real.rpow ((geometricDiscount s p)⁻¹) (q / p) =
                Real.rpow (geometricDiscount s p) (-(q / p)) by
                simpa using
                  (Real.rpow_neg_eq_inv_rpow (geometricDiscount s p) (q / p)).symm]
            rw [hnegdiv]
  calc
    ∑' n : ℕ, geometricWeight s q n * Real.rpow (H n) (q / 2) =
        geometricDiscount s q * ∑' n : ℕ, Real.rpow (A n) (q / p) := hSeries_q
    _ ≤ geometricDiscount s q * Real.rpow (∑' n : ℕ, A n) (q / p) := by
          exact mul_le_mul_of_nonneg_left hArpow_le hdisc_q_nonneg
    _ =
        geometricDiscount s q *
          (Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow
              (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
              (q / p)) := by
            rw [hAsum_rpow_eq]
    _ =
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow
            (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
            (q / p) := by
            ring

private theorem geometricDiscount_change_factor_nonneg {s p q : ℝ}
    (hs : 0 < s) (hp : 0 < p) (hq : 0 < q) :
    0 ≤ geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) := by
  refine mul_nonneg ?_ ?_
  · simpa [geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg (mul_nonneg hs.le hq.le)
  · exact Real.rpow_nonneg
      (by
        simpa [geometricDiscount_eq_old] using
          Homogenization.geometricDiscount_nonneg (mul_nonneg hs.le hp.le)) _

private theorem geometricDiscount_change_factor_rpow_two_div {s p q : ℝ}
    (hs : 0 < s) (hp : 0 < p) (hq : 0 < q) :
    Real.rpow
        (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
        (2 / q) =
      Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p) := by
  have hdisc_q_nonneg : 0 ≤ geometricDiscount s q := by
    simpa [geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg (mul_nonneg hs.le hq.le)
  have hdisc_p_nonneg : 0 ≤ geometricDiscount s p := by
    simpa [geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg (mul_nonneg hs.le hp.le)
  have hdisc_p_pow_nonneg :
      0 ≤ Real.rpow (geometricDiscount s p) (-q / p) :=
    Real.rpow_nonneg hdisc_p_nonneg _
  have hmul : (-q / p : ℝ) * (2 / q) = -2 / p := by
    field_simp [hq.ne', hp.ne']
  have hrpow :
      Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) =
        Real.rpow (geometricDiscount s p) (-2 / p) := by
    calc
      Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) =
          Real.rpow (geometricDiscount s p) ((-q / p) * (2 / q)) := by
            symm
            exact Real.rpow_mul hdisc_p_nonneg (-q / p) (2 / q)
      _ = Real.rpow (geometricDiscount s p) (-2 / p) := by
            rw [hmul]
  have hfac :
      Real.rpow
          (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
          (2 / q) =
        Real.rpow (geometricDiscount s q) (2 / q) *
          Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) :=
    Real.mul_rpow hdisc_q_nonneg hdisc_p_pow_nonneg
  rw [hfac, hrpow]

theorem LambdaSqFinite_le_change_exponent_geometricDiscount {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q) :
    LambdaSq Q s (.finite q) a ≤
      Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p) *
        LambdaSq Q s (.finite p) a := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hsum_p := summable_B_series_pointwiseCoeffField Q a hs hp
  have hSeries :=
    book_geometricWeight_changeOfQ_tsum_le (hs := hs) (hp1 := hp1) (hpq := hpq)
      (H := fun n => maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
      (fun n =>
        let hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a)
      hsum_p
  have hLambdaQ_nonneg : 0 ≤ LambdaSq Q s (.finite q) a :=
    Real.rpow_nonneg
      (LambdaSqFinite_series_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le)) _
  have hLambdaP_nonneg : 0 ≤ LambdaSq Q s (.finite p) a :=
    Real.rpow_nonneg
      (LambdaSqFinite_series_nonneg Q s p a hp.le (mul_nonneg hs.le hp.le)) _
  have hLambdaP_rpow :
      Real.rpow
          (∑' n : ℕ,
            geometricWeight s p n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (p / 2))
          (q / p) =
        Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
    have hmul : (p / 2 : ℝ) * (q / p) = q / 2 := by
      field_simp [hp.ne']
    calc
      Real.rpow
          (∑' n : ℕ,
            geometricWeight s p n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (p / 2))
          (q / p) =
          Real.rpow (Real.rpow (LambdaSq Q s (.finite p) a) (p / 2)) (q / p) := by
            rw [← LambdaSqFinite_rpow_q_div_two_eq_tsum Q s p a hp
              (mul_nonneg hs.le hp.le)]
      _ = Real.rpow (LambdaSq Q s (.finite p) a) ((p / 2) * (q / p)) := by
            symm
            exact Real.rpow_mul hLambdaP_nonneg (p / 2) (q / p)
      _ = Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
            rw [hmul]
  have hpow :
      Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) ≤
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
    calc
      Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) =
          ∑' n : ℕ,
            geometricWeight s q n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (q / 2) := by
            exact LambdaSqFinite_rpow_q_div_two_eq_tsum Q s q a hq
              (mul_nonneg hs.le hq.le)
      _ ≤
          geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow
              (∑' n : ℕ,
                geometricWeight s p n *
                  Real.rpow
                    (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                    (p / 2))
              (q / p) := hSeries
      _ =
          geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
            rw [hLambdaP_rpow]
  have hfactor_nonneg :
      0 ≤ geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) :=
    geometricDiscount_change_factor_nonneg hs hp hq
  calc
    LambdaSq Q s (.finite q) a ≤
        Real.rpow
            (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
            (2 / q) *
          LambdaSq Q s (.finite p) a := by
          exact Homogenization.le_rpow_factor_mul_of_rpow_q_div_two_le hq
            hLambdaQ_nonneg hLambdaP_nonneg hfactor_nonneg hpow
    _ =
        Real.rpow (geometricDiscount s q) (2 / q) *
          Real.rpow (geometricDiscount s p) (-2 / p) *
          LambdaSq Q s (.finite p) a := by
            rw [geometricDiscount_change_factor_rpow_two_div hs hp hq]

theorem lambdaSqFinite_inv_le_change_exponent_geometricDiscount {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q) :
    (lambdaSq Q s (.finite q) a)⁻¹ ≤
      Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p) *
        (lambdaSq Q s (.finite p) a)⁻¹ := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hsum_p := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs hp
  have hSeries :=
    book_geometricWeight_changeOfQ_tsum_le (hs := hs) (hp1 := hp1) (hpq := hpq)
      (H := fun n =>
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
      (fun n =>
        let hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a)
      hsum_p
  have hlambdaQ_nonneg : 0 ≤ lambdaSq Q s (.finite q) a :=
    Real.rpow_nonneg
      (lambdaSqFinite_series_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le)) _
  have hlambdaP_nonneg : 0 ≤ lambdaSq Q s (.finite p) a :=
    Real.rpow_nonneg
      (lambdaSqFinite_series_nonneg Q s p a hp.le (mul_nonneg hs.le hp.le)) _
  have hLambdaQ_inv_nonneg : 0 ≤ (lambdaSq Q s (.finite q) a)⁻¹ :=
    inv_nonneg.mpr hlambdaQ_nonneg
  have hLambdaP_inv_nonneg : 0 ≤ (lambdaSq Q s (.finite p) a)⁻¹ :=
    inv_nonneg.mpr hlambdaP_nonneg
  have hlambdaP_rpow :
      Real.rpow
          (∑' n : ℕ,
            geometricWeight s p n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (p / 2))
          (q / p) =
        Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
    have hmul_neg : (-p / 2 : ℝ) * (q / p) = -q / 2 := by
      field_simp [hp.ne']
    calc
      Real.rpow
          (∑' n : ℕ,
            geometricWeight s p n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (p / 2))
          (q / p) =
          Real.rpow (Real.rpow (lambdaSq Q s (.finite p) a) (-p / 2)) (q / p) := by
            rw [← lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s p a hp
              (mul_nonneg hs.le hp.le)]
      _ = Real.rpow (lambdaSq Q s (.finite p) a) ((-p / 2) * (q / p)) := by
            symm
            exact Real.rpow_mul hlambdaP_nonneg (-p / 2) (q / p)
      _ = Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
            rw [hmul_neg]
  have hpow :
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) ≤
        (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p)) *
          Real.rpow ((lambdaSq Q s (.finite p) a)⁻¹) (q / 2) := by
    have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
    calc
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) =
          Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2)).symm
      _ =
          ∑' n : ℕ,
            geometricWeight s q n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (q / 2) := by
            exact lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s q a hq
              (mul_nonneg hs.le hq.le)
      _ ≤
          geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow
              (∑' n : ℕ,
                geometricWeight s p n *
                  Real.rpow
                    (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                    (p / 2))
              (q / p) := hSeries
      _ =
          geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
            rw [hlambdaP_rpow]
      _ =
          (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p)) *
            Real.rpow ((lambdaSq Q s (.finite p) a)⁻¹) (q / 2) := by
            rw [show Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) =
                Real.rpow ((lambdaSq Q s (.finite p) a)⁻¹) (q / 2) by
                simpa [hneg] using
                  (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite p) a) (q / 2))]
  have hfactor_nonneg :
      0 ≤ geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) :=
    geometricDiscount_change_factor_nonneg hs hp hq
  calc
    (lambdaSq Q s (.finite q) a)⁻¹ ≤
        Real.rpow
            (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
            (2 / q) *
          (lambdaSq Q s (.finite p) a)⁻¹ := by
          exact Homogenization.le_rpow_factor_mul_of_rpow_q_div_two_le hq
            hLambdaQ_inv_nonneg hLambdaP_inv_nonneg hfactor_nonneg hpow
    _ =
        Real.rpow (geometricDiscount s q) (2 / q) *
          Real.rpow (geometricDiscount s p) (-2 / p) *
          (lambdaSq Q s (.finite p) a)⁻¹ := by
            rw [geometricDiscount_change_factor_rpow_two_div hs hp hq]

end

end Ch02
end Book
end Homogenization
