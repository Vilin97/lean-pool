/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.EllipticityFiniteQ.Series

/-! # Change Of Q -/

namespace Homogenization

noncomputable section

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

theorem le_rpow_factor_mul_of_rpow_q_div_two_le {A B F q : ℝ} (hq : 0 < q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hAB : Real.rpow A (q / 2) ≤ F * Real.rpow B (q / 2)) :
    A ≤ Real.rpow F (2 / q) * B := by
  apply le_of_rpow_q_div_two_le hq hA
    (mul_nonneg (Real.rpow_nonneg hF _) hB)
  calc
    Real.rpow A (q / 2) ≤ F * Real.rpow B (q / 2) := hAB
    _ = Real.rpow (Real.rpow F (2 / q) * B) (q / 2) := by
      have hmul : (2 / q : ℝ) * (q / 2) = 1 := by
        field_simp [hq.ne']
      have hFpow : Real.rpow (Real.rpow F (2 / q)) (q / 2) = F := by
        calc
          Real.rpow (Real.rpow F (2 / q)) (q / 2) = Real.rpow F ((2 / q) * (q / 2)) := by
            exact (Real.rpow_mul hF (2 / q) (q / 2)).symm
          _ = Real.rpow F 1 := by simp [hmul]
          _ = F := by exact Real.rpow_one F
      calc
        F * Real.rpow B (q / 2) = Real.rpow (Real.rpow F (2 / q)) (q / 2) * Real.rpow B (q / 2) := by
          rw [hFpow]
        _ = Real.rpow (Real.rpow F (2 / q) * B) (q / 2) := by
          exact (Real.mul_rpow (Real.rpow_nonneg hF _) hB).symm


private theorem geometricWeight_changeOfQ_tsum_le {H : ℕ → ℝ} {s p q : ℝ}
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
  have hdisc_p_pos : 0 < geometricDiscount s p := geometricDiscount_pos (mul_pos hs hp)
  have hdisc_q_nonneg : 0 ≤ geometricDiscount s q := by
    exact geometricDiscount_nonneg (mul_nonneg hs.le hq.le)
  have hAweighted :
      Summable (fun n : ℕ => geometricDiscount s p * A n) := by
    simpa [A, geometricWeight, mul_assoc, mul_left_comm, mul_comm] using hsum_p
  have hAsum : Summable A := (summable_mul_left_iff hdisc_p_pos.ne').1 hAweighted
  have hArpow_sum : Summable (fun n : ℕ => Real.rpow (A n) (q / p)) :=
    summable_rpow_of_nonneg_of_one_le hq_div hA_nonneg hAsum
  have hArpow_le :
      ∑' n : ℕ, Real.rpow (A n) (q / p) ≤ Real.rpow (∑' n : ℕ, A n) (q / p) :=
    tsum_rpow_le_rpow_tsum_of_nonneg hq_div hA_nonneg hAsum
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
              exact Real.mul_rpow (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
                (Real.rpow_nonneg (hH_nonneg n) _)
      _ =
          Real.rpow (3 : ℝ) ((-s * p * (n : ℝ)) * (q / p)) *
            Real.rpow (H n) ((p / 2) * (q / p)) := by
              congr 1
              · symm
                exact Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s * p * (n : ℝ)) (q / p)
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
      geometricDiscount s p * ∑' n : ℕ, A n = ∑' n : ℕ, geometricDiscount s p * A n := by
            symm
            simpa using (Summable.tsum_mul_left (geometricDiscount s p) hAsum)
      _ = ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
            apply tsum_congr
            intro n
            simp [A, geometricWeight, mul_assoc, mul_left_comm, mul_comm]
  have hSeries_p_nonneg :
      0 ≤ ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
    refine tsum_nonneg ?_
    intro n
    exact mul_nonneg (geometricWeight_nonneg n (mul_nonneg hs.le hp.le))
      (Real.rpow_nonneg (hH_nonneg n) _)
  have hAsum_eq :
      ∑' n : ℕ, A n =
        (geometricDiscount s p)⁻¹ *
          ∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2) := by
    calc
      ∑' n : ℕ, A n =
          ((geometricDiscount s p)⁻¹ * geometricDiscount s p) * ∑' n : ℕ, A n := by
            rw [inv_mul_cancel₀ hdisc_p_pos.ne', one_mul]
      _ = (geometricDiscount s p)⁻¹ * (geometricDiscount s p * ∑' n : ℕ, A n) := by ring
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
            exact Real.mul_rpow (inv_nonneg.mpr (geometricDiscount_nonneg (mul_nonneg hs.le hp.le)))
              hSeries_p_nonneg
      _ =
          Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow
              (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
              (q / p) := by
            have hnegdiv : -(q / p) = -q / p := by ring
            simpa [hnegdiv] using
              show Real.rpow ((geometricDiscount s p)⁻¹) (q / p) *
                    Real.rpow
                      (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
                      (q / p) =
                  Real.rpow (geometricDiscount s p) (-(q / p)) *
                    Real.rpow
                      (∑' n : ℕ, geometricWeight s p n * Real.rpow (H n) (p / 2))
                      (q / p) by
                rw [show Real.rpow ((geometricDiscount s p)⁻¹) (q / p) =
                    Real.rpow (geometricDiscount s p) (-(q / p)) by
                    simpa using
                      (Real.rpow_neg_eq_inv_rpow (geometricDiscount s p) (q / p)).symm]
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


theorem multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_le_changeOfQ {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hsum_p :
      Summable (fun n : ℕ =>
        geometricWeight s p n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (p / 2))) :
    Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) ≤
      geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
        Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hSeries :=
    geometricWeight_changeOfQ_tsum_le (hs := hs) (hp1 := hp1) (hpq := hpq)
      (H := fun n => maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
      (fun n =>
        maxDescendantBBlockNormAtScale_nonneg Q
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
      hsum_p
  have hLambdaP_nonneg :
      0 ≤ LambdaSq Q s (.finite p) a := by
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q s p a hp.le (mul_nonneg hs.le hp.le)
  have hmul : (p / 2 : ℝ) * (q / p) = q / 2 := by
    field_simp [hp.ne']
  calc
    Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) =
        ∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
          exact multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum Q s q a hq
            (mul_nonneg hs.le hq.le)
    _ ≤
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow
            (∑' n : ℕ,
              geometricWeight s p n *
                Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (p / 2))
            (q / p) := hSeries
    _ =
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow (Real.rpow (LambdaSq Q s (.finite p) a) (p / 2)) (q / p) := by
            rw [← multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum Q s p a hp
              (mul_nonneg hs.le hp.le)]
    _ =
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
            have hrpow :
                Real.rpow (Real.rpow (LambdaSq Q s (.finite p) a) (p / 2)) (q / p) =
                  Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
              calc
                Real.rpow (Real.rpow (LambdaSq Q s (.finite p) a) (p / 2)) (q / p) =
                    Real.rpow (LambdaSq Q s (.finite p) a) ((p / 2) * (q / p)) := by
                      symm
                      exact Real.rpow_mul hLambdaP_nonneg (p / 2) (q / p)
                _ = Real.rpow (LambdaSq Q s (.finite p) a) (q / 2) := by
                      rw [hmul]
            rw [hrpow]

theorem multiscale_ellipticity_LambdaSq_finite_le_changeOfQ {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hsum_p :
      Summable (fun n : ℕ =>
        geometricWeight s p n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (p / 2))) :
    LambdaSq Q s (.finite q) a ≤
      Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p) *
        LambdaSq Q s (.finite p) a := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hpow :=
    multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_le_changeOfQ
      Q a hs hp1 hpq hsum_p
  have hLambdaQ_nonneg :
      0 ≤ LambdaSq Q s (.finite q) a := by
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le)
  have hLambdaP_nonneg :
      0 ≤ LambdaSq Q s (.finite p) a := by
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q s p a hp.le (mul_nonneg hs.le hp.le)
  have hfactor_nonneg :
      0 ≤ geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) := by
    refine mul_nonneg (geometricDiscount_nonneg (mul_nonneg hs.le hq.le)) ?_
    exact Real.rpow_nonneg (geometricDiscount_nonneg (mul_nonneg hs.le hp.le)) _
  calc
    LambdaSq Q s (.finite q) a ≤
        Real.rpow
            (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
            (2 / q) *
          LambdaSq Q s (.finite p) a := by
          exact le_rpow_factor_mul_of_rpow_q_div_two_le hq hLambdaQ_nonneg hLambdaP_nonneg
            hfactor_nonneg hpow
    _ =
        Real.rpow (geometricDiscount s q) (2 / q) *
          Real.rpow (geometricDiscount s p) (-2 / p) *
          LambdaSq Q s (.finite p) a := by
            have hdisc_q_nonneg : 0 ≤ geometricDiscount s q := by
              exact geometricDiscount_nonneg (mul_nonneg hs.le hq.le)
            have hdisc_p_pow_nonneg : 0 ≤ Real.rpow (geometricDiscount s p) (-q / p) := by
              exact Real.rpow_nonneg (geometricDiscount_nonneg (mul_nonneg hs.le hp.le)) _
            have hmul : (-q / p : ℝ) * (2 / q) = -2 / p := by
              field_simp [hq.ne', hp.ne']
            have hrpow :
                Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) =
                  Real.rpow (geometricDiscount s p) (-2 / p) := by
              calc
                Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) =
                    Real.rpow (geometricDiscount s p) ((-q / p) * (2 / q)) := by
                      symm
                      exact Real.rpow_mul
                        (geometricDiscount_nonneg (mul_nonneg hs.le hp.le))
                        (-q / p) (2 / q)
                _ = Real.rpow (geometricDiscount s p) (-2 / p) := by
                      rw [hmul]
            have hfac :
                Real.rpow
                    (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
                    (2 / q) =
                  Real.rpow (geometricDiscount s q) (2 / q) *
                    Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) := by
              exact Real.mul_rpow hdisc_q_nonneg hdisc_p_pow_nonneg
            calc
              Real.rpow
                    (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
                    (2 / q) *
                  LambdaSq Q s (.finite p) a =
                  (Real.rpow (geometricDiscount s q) (2 / q) *
                      Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q)) *
                    LambdaSq Q s (.finite p) a := by
                        rw [hfac]
              _ =
                  (Real.rpow (geometricDiscount s q) (2 / q) *
                      Real.rpow (geometricDiscount s p) (-2 / p)) *
                    LambdaSq Q s (.finite p) a := by
                        rw [hrpow]
              _ =
                  Real.rpow (geometricDiscount s q) (2 / q) *
                    Real.rpow (geometricDiscount s p) (-2 / p) *
                    LambdaSq Q s (.finite p) a := by ring

theorem multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_le_changeOfQ {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hsum_p :
      Summable (fun n : ℕ =>
        geometricWeight s p n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (p / 2))) :
    Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) ≤
      geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
        Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hSeries :=
    geometricWeight_changeOfQ_tsum_le (hs := hs) (hp1 := hp1) (hpq := hpq)
      (H := fun n => maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
      (fun n =>
        maxDescendantSigmaStarInvNormAtScale_nonneg Q
          (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
      hsum_p
  have hlambdaP_nonneg :
      0 ≤ lambdaSq Q s (.finite p) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s p a hp.le (mul_nonneg hs.le hp.le)
  have hmul_neg : (-p / 2 : ℝ) * (q / p) = -q / 2 := by
    field_simp [hp.ne']
  calc
    Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) =
        ∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
          exact multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum Q s q a hq
            (mul_nonneg hs.le hq.le)
    _ ≤
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow
            (∑' n : ℕ,
              geometricWeight s p n *
                Real.rpow
                  (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
                  (p / 2))
            (q / p) := hSeries
    _ =
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow (Real.rpow (lambdaSq Q s (.finite p) a) (-p / 2)) (q / p) := by
            rw [← multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum Q s p a hp
              (mul_nonneg hs.le hp.le)]
    _ =
        geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
          Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
            have hrpow :
                Real.rpow (Real.rpow (lambdaSq Q s (.finite p) a) (-p / 2)) (q / p) =
                  Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
              calc
                Real.rpow (Real.rpow (lambdaSq Q s (.finite p) a) (-p / 2)) (q / p) =
                    Real.rpow (lambdaSq Q s (.finite p) a) ((-p / 2) * (q / p)) := by
                      symm
                      exact Real.rpow_mul hlambdaP_nonneg (-p / 2) (q / p)
                _ = Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := by
                      rw [hmul_neg]
            rw [hrpow]

theorem multiscale_ellipticity_lambdaSq_finite_inv_le_changeOfQ {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s p q : ℝ}
    (hs : 0 < s) (hp1 : 1 ≤ p) (hpq : p ≤ q)
    (hsum_p :
      Summable (fun n : ℕ =>
        geometricWeight s p n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (p / 2))) :
    (lambdaSq Q s (.finite q) a)⁻¹ ≤
      Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p) *
        (lambdaSq Q s (.finite p) a)⁻¹ := by
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hpow :=
    multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_le_changeOfQ
      Q a hs hp1 hpq hsum_p
  have hpow' :
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) ≤
        (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p)) *
          Real.rpow ((lambdaSq Q s (.finite p) a)⁻¹) (q / 2) := by
    have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
    calc
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) =
          Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2)).symm
      _ ≤
          geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow (lambdaSq Q s (.finite p) a) (-q / 2) := hpow
      _ =
          geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) *
            Real.rpow ((lambdaSq Q s (.finite p) a)⁻¹) (q / 2) := by
              congr 1
              simpa [hneg] using
                (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite p) a) (q / 2))
  have hLambdaQ_inv_nonneg :
      0 ≤ (lambdaSq Q s (.finite q) a)⁻¹ := by
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le))
  have hLambdaP_inv_nonneg :
      0 ≤ (lambdaSq Q s (.finite p) a)⁻¹ := by
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q s p a hp.le (mul_nonneg hs.le hp.le))
  have hfactor_nonneg :
      0 ≤ geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p) := by
    refine mul_nonneg (geometricDiscount_nonneg (mul_nonneg hs.le hq.le)) ?_
    exact Real.rpow_nonneg (geometricDiscount_nonneg (mul_nonneg hs.le hp.le)) _
  calc
    (lambdaSq Q s (.finite q) a)⁻¹ ≤
        Real.rpow
            (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
            (2 / q) *
          (lambdaSq Q s (.finite p) a)⁻¹ := by
          exact le_rpow_factor_mul_of_rpow_q_div_two_le hq hLambdaQ_inv_nonneg hLambdaP_inv_nonneg
            hfactor_nonneg hpow'
    _ =
        Real.rpow (geometricDiscount s q) (2 / q) *
          Real.rpow (geometricDiscount s p) (-2 / p) *
          (lambdaSq Q s (.finite p) a)⁻¹ := by
            have hdisc_q_nonneg : 0 ≤ geometricDiscount s q := by
              exact geometricDiscount_nonneg (mul_nonneg hs.le hq.le)
            have hdisc_p_pow_nonneg : 0 ≤ Real.rpow (geometricDiscount s p) (-q / p) := by
              exact Real.rpow_nonneg (geometricDiscount_nonneg (mul_nonneg hs.le hp.le)) _
            have hmul : (-q / p : ℝ) * (2 / q) = -2 / p := by
              field_simp [hq.ne', hp.ne']
            have hrpow :
                Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) =
                  Real.rpow (geometricDiscount s p) (-2 / p) := by
              calc
                Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) =
                    Real.rpow (geometricDiscount s p) ((-q / p) * (2 / q)) := by
                      symm
                      exact Real.rpow_mul
                        (geometricDiscount_nonneg (mul_nonneg hs.le hp.le))
                        (-q / p) (2 / q)
                _ = Real.rpow (geometricDiscount s p) (-2 / p) := by
                      rw [hmul]
            have hfac :
                Real.rpow
                    (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
                    (2 / q) =
                  Real.rpow (geometricDiscount s q) (2 / q) *
                    Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q) := by
              exact Real.mul_rpow hdisc_q_nonneg hdisc_p_pow_nonneg
            calc
              Real.rpow
                    (geometricDiscount s q * Real.rpow (geometricDiscount s p) (-q / p))
                    (2 / q) *
                  (lambdaSq Q s (.finite p) a)⁻¹ =
                  (Real.rpow (geometricDiscount s q) (2 / q) *
                      Real.rpow (Real.rpow (geometricDiscount s p) (-q / p)) (2 / q)) *
                    (lambdaSq Q s (.finite p) a)⁻¹ := by
                        rw [hfac]
              _ =
                  (Real.rpow (geometricDiscount s q) (2 / q) *
                      Real.rpow (geometricDiscount s p) (-2 / p)) *
                    (lambdaSq Q s (.finite p) a)⁻¹ := by
                        rw [hrpow]
              _ =
                  Real.rpow (geometricDiscount s q) (2 / q) *
                    Real.rpow (geometricDiscount s p) (-2 / p) *
                    (lambdaSq Q s (.finite p) a)⁻¹ := by ring


end

end Homogenization
