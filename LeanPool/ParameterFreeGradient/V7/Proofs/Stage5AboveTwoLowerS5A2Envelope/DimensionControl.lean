/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.KernelCocoercivity
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5AGlobalC2.QuadraticBound

/-!
Dimension-dependent norm comparisons yield the kernel Hessian and cocoercivity bounds.
-/

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AFinalRepair
open Stage5AboveTwoLower.S5AGlobalC2

/-- The explicit ambient comparison constant is the expected real power. -/
lemma lpAmbientConstant_eq_rpow {s : ℝ} (hs : 0 < s) {d : ℕ} :
    lpAmbientConstant s d = (d : ℝ) ^ (1 / s) := by
  simp [lpAmbientConstant,
    ENNReal.toReal_ofReal hs.le, NNReal.coe_rpow]

/-- In the logarithmic regime the finite-dimensional norm conversion costs
only the fixed factor `exp (1/3)`. -/
lemma lpNorm_kernelR0_le_exp_mul_lpNorm {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) (hregime : ¬ p ≤ 3 * Real.log d)
    (x : Point d) :
    lpNorm (kernelR0 p d) x ≤ Real.exp (1 / 3) * lpNorm p x := by
  have hr : kernelR0 p d = 3 * Real.log d := by
    rw [kernelR0, min_eq_right (le_of_not_ge hregime)]
  have hrpos : 0 < kernelR0 p d :=
    (two_lt_kernelR0 hp hd).trans' (by norm_num)
  have hrtwo : 2 < kernelR0 p d := two_lt_kernelR0 hp hd
  calc
    lpNorm (kernelR0 p d) x ≤
        lpAmbientConstant (kernelR0 p d) d * ‖x‖ :=
      lpNorm_le_ambientConstant (by linarith [hrtwo]) x
    _ ≤ lpAmbientConstant (kernelR0 p d) d * lpNorm p x := by
      gcongr
      · exact lpAmbientConstant_nonneg _ _
      · exact norm_le_lpNorm (by linarith) x
    _ = Real.exp (1 / 3) * lpNorm p x := by
      congr 1
      rw [lpAmbientConstant_eq_rpow hrpos, hr]
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
      rw [← Real.exp_log hdpos, ← Real.exp_mul]
      congr 1
      rw [Real.log_exp]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one hdpos
        (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hd)))]

/-- The repaired parameter leaves enough slack to absorb both occurrences of
the logarithmic-regime finite-dimensional norm conversion. -/
lemma repair_logarithmic_hessian_scalar_bound {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) (hregime : ¬ p ≤ 3 * Real.log d) :
    4 * repairTheta p d * (kernelR0 p d - 1) *
        Real.exp (2 * repairTheta p d / 3) ≤
      15 * Real.exp (2 / 3) * Real.log d := by
  have hr : kernelR0 p d = 3 * Real.log d := by
    rw [kernelR0, min_eq_right (le_of_not_ge hregime)]
  have hlog : 0 < Real.log d := by
    exact Real.log_pos (by exact_mod_cast
      (lt_of_lt_of_le (by decide : 1 < 2) hd))
  have hcoeff := repair_hessian_coefficient_lt_101_div_25_mul_r0 hp hd
  rw [hr] at hcoeff
  have htheta := repairTheta_lt_101_div_100 hp hd
  have hexparg : 2 * repairTheta p d / 3 ≤ 101 / 150 := by
    linarith
  have hexp : Real.exp (2 * repairTheta p d / 3) ≤
      Real.exp (2 / 3) * (150 / 149) := by
    calc
      Real.exp (2 * repairTheta p d / 3) ≤ Real.exp (101 / 150) :=
        Real.exp_le_exp.mpr hexparg
      _ = Real.exp (2 / 3) * Real.exp (1 / 150) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (2 / 3) * (150 / 149) := by
        gcongr
        have hs := Real.exp_bound_div_one_sub_of_interval
          (x := (1 / 150 : ℝ)) (by norm_num) (by norm_num)
        norm_num at hs ⊢
        exact hs
  have hcoeffNonneg : 0 ≤
      4 * repairTheta p d * (kernelR0 p d - 1) := by
    have ht := one_lt_repairTheta hp hd
    have hrpos := two_lt_kernelR0 hp hd
    nlinarith [mul_pos (by positivity : 0 < 4 * repairTheta p d)
      (by linarith : 0 < kernelR0 p d - 1)]
  have hmul := mul_le_mul hcoeff.le hexp (Real.exp_pos _).le
    (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hlog.le))
  rw [hr]
  nlinarith [Real.exp_pos (2 / 3)]

/-- The literal repaired kernel Hessian obeys the exact frozen two-regime
constant on the physical unit `ell_p` ball. -/
theorem repair_kernelHessian_unit_bound {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) (z e : Point d)
    (hz : lpNorm p z ≤ 1) :
    O3.pairing e
        (kernelHessian (kernelR0 p d) (repairTheta p d) z e) ≤
      (if p ≤ 3 * Real.log d then 5 * p
       else 15 * Real.exp (2 / 3) * Real.log d) *
        lpNorm p e ^ (2 : ℕ) := by
  let r := kernelR0 p d
  let theta := repairTheta p d
  have hr : 2 < r := two_lt_kernelR0 hp hd
  have htheta : 1 < theta := one_lt_repairTheta hp hd
  have htr : 2 * theta < r := two_mul_repairTheta_lt_kernelR0 hp hd
  have hraw := kernelHessian_quadratic_bound hr htheta htr z e
  change O3.pairing e (kernelHessian r theta z e) ≤
    (if p ≤ 3 * Real.log d then 5 * p
     else 15 * Real.exp (2 / 3) * Real.log d) *
      lpNorm p e ^ (2 : ℕ)
  by_cases hregime : p ≤ 3 * Real.log d
  · rw [ite_eq_left hregime]
    have hrp : r = p := by simp [r, kernelR0, min_eq_left hregime]
    have ha : 0 ≤ 2 * theta - 2 := by linarith
    have hzpow : lpNorm r z ^ (2 * theta - 2) ≤ 1 := by
      rw [hrp]
      exact Real.rpow_le_one (O3.lpNorm_nonneg p z) hz ha
    have hcoeff : 4 * theta * (r - 1) ≤ 5 * p := by
      have hc := repair_hessian_coefficient_lt_101_div_25_mul_r0 hp hd
      dsimp [r, theta]
      rw [kernelR0, min_eq_left hregime] at hc ⊢
      nlinarith
    rw [hrp] at hraw hzpow ⊢
    have hcoeffp : 4 * theta * (p - 1) ≤ 5 * p := by
      simpa [hrp] using hcoeff
    have hcoefNonneg : 0 ≤ 4 * theta * (p - 1) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    have heNonneg : 0 ≤ lpNorm p e ^ (2 : ℕ) := sq_nonneg _
    calc
      O3.pairing e (kernelHessian p theta z e) ≤
          4 * theta * (p - 1) * lpNorm p z ^ (2 * theta - 2) *
            lpNorm p e ^ (2 : ℕ) := hraw
      _ ≤ (4 * theta * (p - 1)) * 1 * lpNorm p e ^ (2 : ℕ) := by
        gcongr
      _ = (4 * theta * (p - 1)) * lpNorm p e ^ (2 : ℕ) := by ring
      _ ≤ 5 * p * lpNorm p e ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcoeffp heNonneg
  · rw [ite_eq_right hregime]
    let K : ℝ := Real.exp (1 / 3)
    have hKpos : 0 < K := Real.exp_pos _
    have hzconv := lpNorm_kernelR0_le_exp_mul_lpNorm hp hd hregime z
    have heconv := lpNorm_kernelR0_le_exp_mul_lpNorm hp hd hregime e
    change lpNorm r z ≤ K * lpNorm p z at hzconv
    change lpNorm r e ≤ K * lpNorm p e at heconv
    have hzK : lpNorm r z ≤ K := by
      calc
        lpNorm r z ≤ K * lpNorm p z := hzconv
        _ ≤ K * 1 := by gcongr
        _ = K := mul_one K
    have ha : 0 ≤ 2 * theta - 2 := by linarith
    have hzpow : lpNorm r z ^ (2 * theta - 2) ≤
        Real.exp ((2 * theta - 2) / 3) := by
      calc
        lpNorm r z ^ (2 * theta - 2) ≤ K ^ (2 * theta - 2) :=
          Real.rpow_le_rpow (O3.lpNorm_nonneg r z) hzK ha
        _ = Real.exp ((2 * theta - 2) / 3) := by
          dsimp [K]
          rw [← Real.exp_mul]
          congr 1
          ring
    have hesq : lpNorm r e ^ (2 : ℕ) ≤
        (K * lpNorm p e) ^ (2 : ℕ) := by
      nlinarith [O3.lpNorm_nonneg r e, O3.lpNorm_nonneg p e]
    have hcoefNonneg : 0 ≤ 4 * theta * (r - 1) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    have hzpNonneg : 0 ≤ lpNorm r z ^ (2 * theta - 2) :=
      Real.rpow_nonneg (O3.lpNorm_nonneg r z) _
    have htarget := repair_logarithmic_hessian_scalar_bound hp hd hregime
    change 4 * theta * (r - 1) * Real.exp (2 * theta / 3) ≤
      15 * Real.exp (2 / 3) * Real.log d at htarget
    calc
      O3.pairing e (kernelHessian r theta z e) ≤
          4 * theta * (r - 1) * lpNorm r z ^ (2 * theta - 2) *
            lpNorm r e ^ (2 : ℕ) := hraw
      _ ≤ 4 * theta * (r - 1) *
          Real.exp ((2 * theta - 2) / 3) *
            (K * lpNorm p e) ^ (2 : ℕ) := by
        gcongr
      _ = (4 * theta * (r - 1) * Real.exp (2 * theta / 3)) *
          lpNorm p e ^ (2 : ℕ) := by
        dsimp [K]
        rw [mul_pow]
        rw [show (Real.exp (1 / 3)) ^ (2 : ℕ) = Real.exp (2 / 3) by
          rw [← Real.exp_nat_mul]; congr 1; ring]
        have hexpid : Real.exp ((2 * theta - 2) / 3) * Real.exp (2 / 3) =
            Real.exp (2 * theta / 3) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          4 * theta * (r - 1) * Real.exp ((2 * theta - 2) / 3) *
              (Real.exp (2 / 3) * lpNorm p e ^ (2 : ℕ)) =
              (4 * theta * (r - 1)) *
                (Real.exp ((2 * theta - 2) / 3) * Real.exp (2 / 3)) *
                  lpNorm p e ^ (2 : ℕ) := by ring
          _ = (4 * theta * (r - 1) * Real.exp (2 * theta / 3)) *
                lpNorm p e ^ (2 : ℕ) := by rw [hexpid]
      _ ≤ (15 * Real.exp (2 / 3) * Real.log d) *
          lpNorm p e ^ (2 : ℕ) := by
        gcongr

/-- Exact cocoercivity with the frozen two-regime `Mpd`. -/
theorem repair_kernelGradient_cocoercive {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    KernelCocoerciveOnUnit p
      (if p ≤ 3 * Real.log d then 5 * p
       else 15 * Real.exp (2 / 3) * Real.log d)
      (kernelGradientVector (d := d) (kernelR0 p d) (repairTheta p d)) := by
  have hM : 0 ≤
      (if p ≤ 3 * Real.log d then 5 * p
       else 15 * Real.exp (2 / 3) * Real.log d) := by
    split_ifs
    · positivity
    · have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast
        (lt_of_lt_of_le (by decide : 1 < 2) hd))
      positivity
  exact kernelGradient_cocoercive_on_unit_of_hessian_bound
    (by linarith) (two_lt_kernelR0 hp hd) (one_lt_repairTheta hp hd)
    (two_mul_repairTheta_lt_kernelR0 hp hd)
    (repair_kernelHessian_unit_bound hp hd)

end V7.Stage5AboveTwoLowerS5A2Envelope
