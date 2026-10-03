/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeUniform
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds

/-! Conditional comparison of the diffusivity chain with its auxiliary
κ′ chain.  The explicit one-step relative error is kept as a hypothesis; the
cutoff averaging estimate that supplies it is a separate analytic task. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- The product loss in comparing recurrences with relative one-step errors. -/
def kappaAtPrimeErrorEnvelope (η : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, d + 1 => (1 - η (m + 1))⁻¹ *
      kappaAtPrimeErrorEnvelope η (m + 1) d

/-- Stability of one positive recurrence step under a relative increment error. -/
theorem positive_recurrence_ratio_step {u v B η x R : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hB : 0 < B)
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hR : 0 < R)
    (hruLo : 1 / R ≤ u / v) (hruHi : u / v ≤ R)
    (hrvHi : v / u ≤ R)
    (hstep : |x - (u + B / u)| ≤ η * (B / u)) :
    max (x / (v + B / v)) ((v + B / v) / x) ≤ R / (1 - η) := by
  have hstepBounds :
      u + (1 - η) * (B / u) ≤ x ∧
      x ≤ u + (1 + η) * (B / u) := by
    have habs := abs_le.mp hstep
    constructor <;> linarith
  have hx : 0 < x := by
    have hterm : 0 < (1 - η) * (B / u) := by positivity
    linarith [hstepBounds.1]
  have hy : 0 < v + B / v := by positivity
  have hr : 0 < u / v := div_pos hu hv
  have hz : 0 ≤ B / v ^ 2 := by positivity
  have hz' : 0 ≤ B / v ^ 2 := hz
  have hfactor : 0 < 1 - η := by linarith
  have hinv : (u / v)⁻¹ = v / u := by
    field_simp [ne_of_gt hu, ne_of_gt hv]
  have hruLo' : (1 - η) / R ≤ u / v := by
    calc
      (1 - η) / R ≤ 1 / R := by
        apply div_le_div_of_nonneg_right _ hR.le
        linarith
      _ ≤ u / v := hruLo
  have htermLo : (1 - η) / R ≤ (1 - η) / (u / v) := by
    apply div_le_div_of_nonneg_left hfactor.le hr
    exact hruHi
  have htermInvHi : (1 + η) / (u / v) ≤ (1 + η) * R := by
    have hEq : (1 + η) / (u / v) = (1 + η) * (v / u) := by
      rw [div_eq_mul_inv, hinv]
    rw [hEq]
    exact mul_le_mul_of_nonneg_left hrvHi (by linarith)
  have hfactorHi : (1 + η) * R ≤ R / (1 - η) := by
    apply (le_div_iff₀ hfactor).2
    nlinarith [sq_nonneg η, hR]
  have hrHi : u / v ≤ R / (1 - η) := by
    apply le_trans hruHi
    apply (le_div_iff₀ hfactor).2
    nlinarith [hR, hη0]
  have hweightedLo : (1 - η) / R ≤
      ((u / v) + (1 - η) * (B / v ^ 2) / (u / v)) /
        (1 + B / v ^ 2) := by
    have hmul1 := mul_le_mul_of_nonneg_right hruLo' hz'
    have hmul2 := mul_le_mul_of_nonneg_right htermLo hz'
    have hsum : (1 - η) / R * (1 + B / v ^ 2) ≤
        (u / v) + (1 - η) * (B / v ^ 2) / (u / v) := by
      calc
        (1 - η) / R * (1 + B / v ^ 2) =
            (1 - η) / R + ((1 - η) / R) * (B / v ^ 2) := by ring
        _ ≤ (u / v) + ((1 - η) / (u / v)) * (B / v ^ 2) :=
          add_le_add hruLo' hmul2
        _ = (u / v) + (1 - η) * (B / v ^ 2) / (u / v) := by ring
    exact (le_div_iff₀ (by positivity : 0 < 1 + B / v ^ 2)).2
      (by nlinarith [hsum])
  have hweightedHi :
      ((u / v) + (1 + η) * (B / v ^ 2) / (u / v)) /
          (1 + B / v ^ 2) ≤ R / (1 - η) := by
    have htermInvHi' : (1 + η) / (u / v) ≤ R / (1 - η) :=
      htermInvHi.trans hfactorHi
    have hmul := mul_le_mul_of_nonneg_right htermInvHi' hz'
    have hsum : (u / v) + (1 + η) * (B / v ^ 2) / (u / v) ≤
        (1 + B / v ^ 2) * (R / (1 - η)) := by
      calc
        (u / v) + (1 + η) * (B / v ^ 2) / (u / v) ≤
            R / (1 - η) + (R / (1 - η)) * (B / v ^ 2) := by
          apply add_le_add hrHi
          calc
            (1 + η) * (B / v ^ 2) / (u / v) =
                ((1 + η) / (u / v)) * (B / v ^ 2) := by ring
            _ ≤ (R / (1 - η)) * (B / v ^ 2) := hmul
        _ = (1 + B / v ^ 2) * (R / (1 - η)) := by ring
    exact (div_le_iff₀ (by positivity : 0 < 1 + B / v ^ 2)).2
      (by nlinarith [hsum])
  have hlowRatio :
      (u + (1 - η) * (B / u)) / (v + B / v) =
        ((u / v) + (1 - η) * (B / v ^ 2) / (u / v)) /
          (1 + B / v ^ 2) := by
    field_simp [ne_of_gt hu, ne_of_gt hv]
  have hhighRatio :
      (u + (1 + η) * (B / u)) / (v + B / v) =
        ((u / v) + (1 + η) * (B / v ^ 2) / (u / v)) /
          (1 + B / v ^ 2) := by
    field_simp [ne_of_gt hu, ne_of_gt hv]
  have hxyLo : (1 - η) / R ≤ x / (v + B / v) := by
    calc
      (1 - η) / R ≤
          (u + (1 - η) * (B / u)) / (v + B / v) := by
            rw [hlowRatio]
            exact hweightedLo
      _ ≤ x / (v + B / v) :=
        div_le_div_of_nonneg_right hstepBounds.1 hy.le
  have hxyHi : x / (v + B / v) ≤ R / (1 - η) := by
    calc
      x / (v + B / v) ≤
          (u + (1 + η) * (B / u)) / (v + B / v) :=
            div_le_div_of_nonneg_right hstepBounds.2 hy.le
      _ ≤ R / (1 - η) := by
        rw [hhighRatio]
        exact hweightedHi
  have hInvLo : (R / (1 - η))⁻¹ ≤ x / (v + B / v) := by
    have hEq : (R / (1 - η))⁻¹ = (1 - η) / R := by
      field_simp [ne_of_gt hR, ne_of_gt hfactor]
    rw [hEq]
    exact hxyLo
  have hInvHi : (v + B / v) / x ≤ R / (1 - η) := by
    have hpos : 0 < R / (1 - η) := div_pos hR hfactor
    have hposRatio : 0 < x / (v + B / v) := div_pos hx hy
    have hrecip : 1 / (x / (v + B / v)) ≤ R / (1 - η) := by
      have h := one_div_le_one_div_of_le (inv_pos.mpr hpos) hInvLo
      simpa [one_div] using h
    simpa [one_div, div_eq_mul_inv, inv_div] using hrecip
  exact max_le_iff.mpr ⟨hxyHi, hInvHi⟩

theorem KappaPrimeComparison.kappaAtPrimeErrorEnvelope_pos (η : ℕ → ℝ)
    (hη : ∀ j, 1 ≤ j → η j < 1) (m d : ℕ) :
    0 < kappaAtPrimeErrorEnvelope η m d := by
  induction d generalizing m with
  | zero => simp [kappaAtPrimeErrorEnvelope]
  | succ d ih =>
      rw [kappaAtPrimeErrorEnvelope]
      exact mul_pos (inv_pos.mpr (sub_pos.mpr (hη _ (by omega))))
        (ih (m + 1))

end AVenhance.Infra.Section3
