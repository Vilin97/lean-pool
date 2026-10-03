/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lemma U: scalar path inequalities

Two elementary facts about absolutely continuous scalar paths: the Cauchy–Schwarz bound for
interval integrals, and the energy balance for an integral path.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace AVenhance.Infra.FullTheorem.LemmaU

/-- Cauchy–Schwarz for interval integrals. -/
theorem sq_intervalIntegral_le {f : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hf : IntervalIntegrable f volume s t)
    (hf2 : IntervalIntegrable (fun r => f r ^ 2) volume s t) :
    (∫ r in s..t, f r) ^ 2 ≤ (t - s) * ∫ r in s..t, f r ^ 2 := by
  rcases hst.eq_or_lt with h | h
  · subst h; simp
  · set I := ∫ r in s..t, f r with hI
    set S := ∫ r in s..t, f r ^ 2 with hS
    have hh : 0 < t - s := sub_pos.mpr h
    set m := I / (t - s) with hm
    have hmh : m * (t - s) = I := by rw [hm]; field_simp
    have h0 : 0 ≤ ∫ r in s..t, (f r - m) ^ 2 :=
      intervalIntegral.integral_nonneg hst (fun r _ => sq_nonneg _)
    have hexp : ∫ r in s..t, (f r - m) ^ 2 = S - 2 * m * I + m ^ 2 * (t - s) := by
      have e : (fun r => (f r - m) ^ 2) = fun r => (f r ^ 2 - (2 * m) * f r) + m ^ 2 := by
        funext r; ring
      rw [e, intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hexp] at h0
    have hm2 : m ^ 2 * (t - s) = m * I := by rw [← hmh]; ring
    have h1 : m * I ≤ S := by linarith
    calc I ^ 2 = (t - s) * (m * I) := by rw [← hmh]; ring
      _ ≤ (t - s) * S := by gcongr

/-- Energy balance for a scalar integral path. -/
theorem scalar_path_energy {y q : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hy : ∀ s ∈ Icc (0 : ℝ) t, y s = y 0 - ∫ r in (0 : ℝ)..s, q r)
    (hq : IntervalIntegrable q volume 0 t) :
    ∫ s in (0 : ℝ)..t, 2 * (q s * y s) = y 0 ^ 2 - y t ^ 2 := by
  have hsol : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) (fun s => -q s) (y 0) 0 t y := by
    intro s hs
    have h := hy s hs
    dsimp [AVenhance.Infra.ODE.IsLinearIntegralSolution, AVenhance.Infra.ODE.linearRhs]
    simpa [intervalIntegral.integral_neg, sub_eq_add_neg] using h
  have henergy := AVenhance.Infra.Parabolic.WeakUniqueness.integral_path_energy_identity
    (hab := ht) hsol hq
  have e : ∫ s in (0 : ℝ)..t, 2 * (q s * y s) =
      ∫ s in (0 : ℝ)..t, 2 * inner ℝ (y s) (q s) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp [mul_comm]
  rw [e, henergy]
  simp

end AVenhance.Infra.FullTheorem.LemmaU

end
