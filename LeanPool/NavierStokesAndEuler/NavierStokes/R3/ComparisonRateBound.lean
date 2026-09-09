/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonYoung

@[expose] public section

/-!
# A uniform rate bound from the localized energy estimate

The Sobolev estimate for the cutoff velocity contains fixed multiplicative
constants. They are absorbed into a single coefficient before applying the
uniform Young estimate. The resulting error decays as `1 / R`, and no sign
condition on the energy coefficient or energy value is used.
-/


noncomputable section

namespace NavierStokesR3.ComparisonRateBound

private theorem rpow_le_square_mul_rpow {B Q x p : ℝ}
    (hB : 0 ≤ B) (hx : 0 ≤ x) (hQ : 1 ≤ Q) (hBQ : B ≤ Q * x)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    B ^ p ≤ Q ^ 2 * x ^ p := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  calc
    B ^ p ≤ (Q * x) ^ p := Real.rpow_le_rpow hB hBQ hp0
    _ = Q ^ p * x ^ p := Real.mul_rpow hQ0 hx
    _ ≤ Q ^ (2 : ℝ) * x ^ p := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hQ hp2) (Real.rpow_nonneg hx _)
    _ = Q ^ 2 * x ^ p := by rw [Real.rpow_two]

/-- Fixed constants in the cutoff Sobolev estimate preserve uniform absorption
of the full pressure and transport error. -/
theorem exists_uniform_flux_absorption {C1 C2 S M δ : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hδ : 0 < δ) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      C1 / R * B ^ (3 / 2 : ℝ) +
        C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
          R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤ δ * A ^ 2 + D / R := by
  let Q : ℝ := max 1 (S * max 1 M)
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hSQ : S ≤ Q := by
    calc
      S = S * 1 := by ring
      _ ≤ S * max 1 M := mul_le_mul_of_nonneg_left (le_max_left _ _) hS
      _ ≤ Q := le_max_right _ _
  have hSMQ : S * M ≤ Q :=
    (mul_le_mul_of_nonneg_left (le_max_right 1 M) hS).trans (le_max_right _ _)
  have hQ0 : 0 ≤ Q := (mul_nonneg hS hM).trans hSMQ
  have hQsq1 : 1 ≤ Q ^ 2 := by nlinarith [sq_nonneg (Q - 1)]
  let C : ℝ := (C1 + C2) * Q ^ 2
  have hC : 0 ≤ C := mul_nonneg (add_nonneg hC1 hC2) (sq_nonneg _)
  have hC1Q : C1 * Q ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) (sq_nonneg _)
  have hC2Q : C2 * Q ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) (sq_nonneg _)
  obtain ⟨D, hD, hD_bound⟩ := ComparisonYoung.exists_cutoff_absorption hC hδ
  refine ⟨D, hD, ?_⟩
  intro R hR A hA B hB hSobolev
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hInv : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  let x : ℝ := A + R⁻¹
  have hx : 0 ≤ x := add_nonneg hA hInv
  have hBQ : B ≤ Q * x := by
    calc
      B ≤ S * (A + M / R) := hSobolev
      _ = S * A + (S * M) * R⁻¹ := by ring
      _ ≤ Q * A + Q * R⁻¹ := add_le_add
        (mul_le_mul_of_nonneg_right hSQ hA)
        (mul_le_mul_of_nonneg_right hSMQ hInv)
      _ = Q * x := by dsimp [x]; ring
  have hhalf : B ^ (1 / 2 : ℝ) ≤ Q ^ 2 * x ^ (1 / 2 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hthree : B ^ (3 / 2 : ℝ) ≤ Q ^ 2 * x ^ (3 / 2 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hquarter : B ^ (3 / 4 : ℝ) ≤ Q ^ 2 * x ^ (3 / 4 : ℝ) :=
    rpow_le_square_mul_rpow hB hx hQ1 hBQ (by norm_num) (by norm_num)
  have hhalfOne : B ^ (1 / 2 : ℝ) + 1 ≤ Q ^ 2 * (x ^ (1 / 2 : ℝ) + 1) := by
    calc
      _ ≤ Q ^ 2 * x ^ (1 / 2 : ℝ) + Q ^ 2 := add_le_add hhalf hQsq1
      _ = _ := by ring
  have hfactor : C2 * (B ^ (1 / 2 : ℝ) + 1) ≤ C * (x ^ (1 / 2 : ℝ) + 1) := by
    calc
      _ ≤ C2 * (Q ^ 2 * (x ^ (1 / 2 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hhalfOne hC2
      _ = (C2 * Q ^ 2) * (x ^ (1 / 2 : ℝ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2Q (by positivity)
  have hRminus2 : R ^ (-2 : ℝ) = 1 / R ^ 2 := by
    rw [Real.rpow_neg hRpos.le, Real.rpow_two, one_div]
  have hlinear : A / R + 1 / R ^ 2 = R⁻¹ * A + R ^ (-2 : ℝ) := by
    rw [hRminus2]
    ring
  have hlinear0 : 0 ≤ R⁻¹ * A + R ^ (-2 : ℝ) :=
    add_nonneg (mul_nonneg hInv hA) (Real.rpow_nonneg hRpos.le _)
  have hpressure : C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2)) ≤
      C * (x ^ (1 / 2 : ℝ) + 1) * (R⁻¹ * A + R ^ (-2 : ℝ)) := by
    rw [hlinear, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfactor hlinear0
  have hcommutator : C2 * (R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤
      C * R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by
    calc
      _ = (C2 * R ^ (-7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) := by ring
      _ ≤ (C2 * R ^ (-7 / 4 : ℝ)) * (Q ^ 2 * x ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hquarter (mul_nonneg hC2 (Real.rpow_nonneg hRpos.le _))
      _ = (C2 * Q ^ 2) * (R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) := by ring
      _ ≤ C * (R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC2Q (by positivity)
      _ = _ := by ring
  have htransport : C1 / R * B ^ (3 / 2 : ℝ) ≤
      C * R⁻¹ * x ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ C1 / R * (Q ^ 2 * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hthree (div_nonneg hC1 hRpos.le)
      _ = (C1 * Q ^ 2) * (R⁻¹ * x ^ (3 / 2 : ℝ)) := by ring
      _ ≤ C * (R⁻¹ * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hC1Q (by positivity)
      _ = _ := by ring
  have hsum : C1 / R * B ^ (3 / 2 : ℝ) +
      C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
        R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) ≤
      C * (x ^ (1 / 2 : ℝ) + 1) * (R⁻¹ * A + R ^ (-2 : ℝ)) +
        C * R ^ (-7 / 4 : ℝ) * x ^ (3 / 4 : ℝ) +
        C * R⁻¹ * x ^ (3 / 2 : ℝ) := by
    nlinarith only [hpressure, hcommutator, htransport]
  exact hsum.trans (hD_bound A hA R hR)

/-- One radius-independent constant turns the full localized energy inequality
into the differential inequality required by Gronwall. -/
theorem exists_uniform_rate_bound {C0 C1 C2 S M : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∃ D ≥ 0, ∀ R ≥ 1, ∀ A ≥ 0, ∀ B ≥ 0, B ≤ S * (A + M / R) →
      ∀ E E' G : ℝ,
        (1 / 2 : ℝ) * E' + A ^ 2 ≤ G * E + C0 / R ^ 2 +
          C1 / R * B ^ (3 / 2 : ℝ) +
          C2 * ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
            R ^ (-7 / 4 : ℝ) * B ^ (3 / 4 : ℝ)) →
        E' ≤ 2 * G * E + D / R := by
  obtain ⟨D, hD, hflux⟩ := exists_uniform_flux_absorption hC1 hC2 hS hM
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨2 * (C0 + D), by positivity, ?_⟩
  intro R hR A hA B hB hSobolev E E' G henergy
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRsq : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hC0radius : C0 / R ^ 2 ≤ C0 / R :=
    div_le_div_of_nonneg_left hC0 hRpos hRsq
  have hbound := hflux R hR A hA B hB hSobolev
  have hdivide : 2 * (C0 + D) / R = 2 * (C0 / R + D / R) := by ring
  rw [hdivide]
  nlinarith only [henergy, hbound, hC0radius, sq_nonneg A]

end NavierStokesR3.ComparisonRateBound
