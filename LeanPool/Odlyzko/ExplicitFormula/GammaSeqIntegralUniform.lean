/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GammaSeqLogDerivUniform

/-!
# Gamma Seq Integral Uniform

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gamma seq approx integrand used in the Odlyzko-bound argument. -/
noncomputable def gammaSeqApproxIntegrand (n : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (Ioc 0 (n : ℝ)).indicator
    (fun x ↦ ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)) x

/-- A gamma integral integrand used in the Odlyzko-bound argument. -/
noncomputable def gammaIntegralIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (Ioi 0).indicator
    (fun x ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) x

/-- A gamma vertical majorant used in the Odlyzko-bound argument. -/
noncomputable def gammaVerticalMajorant (a b : ℝ) (x : ℝ) : ℝ :=
  (Ioi 0).indicator
    (fun x ↦ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))) x

theorem integral_gammaSeqApproxIntegrand
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    (∫ x : ℝ, gammaSeqApproxIntegrand n s x) =
      Complex.GammaSeq s n := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn]
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  rfl

theorem integral_gammaIntegralIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ, gammaIntegralIntegrand s x) = Complex.Gamma s := by
  rw [show gammaIntegralIntegrand s =
      (Ioi 0).indicator
        (fun x ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) by rfl]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    show (∫ x : ℝ in Ioi 0,
      (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) =
      Complex.GammaIntegral s by rfl]
  exact (Complex.Gamma_eq_integral hs).symm

theorem rpow_re_sub_one_le_endpoint_sum
    {a b x : ℝ} {s : ℂ}
    (hx : 0 < x) (ha : a ≤ s.re) (hb : s.re ≤ b) :
    x ^ (s.re - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_total x 1 with hx1 | hx1
  · have hpow :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1
        (show a - 1 ≤ s.re - 1 by linarith)
    exact hpow.trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · have hpow :=
      Real.rpow_le_rpow_of_exponent_le hx1
        (show s.re - 1 ≤ b - 1 by linarith)
    exact hpow.trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

end NumberField.Odlyzko
