/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocitySpatialJets

/-! Uniform radius bookkeeping for the primitive spatial velocity jets. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A finite derivative-budget constant, independent of the scale. -/
def amnrSpatialVelocityConstant (N : ℕ) : ℝ :=
  (2 : ℝ) ^ 5 * ((2 : ℝ) ^ 8) ^ (N + 2) * ((N + 2).factorial : ℝ) * ((N : ℝ) + 4) ^ 2

theorem amnrSpatialVelocityConstant_pos (N : ℕ) : 0 < amnrSpatialVelocityConstant N := by
  unfold amnrSpatialVelocityConstant
  positivity

/-- Undoing the stream seminorm produces two powers of the spatial radius
which cancel its stream-amplitude factor E². -/
theorem amnrStreamSpatialEnvelope_gradient {A E : ℝ} (hE : 0 < E) (n : ℕ) :
    amnrStreamSpatialEnvelope A E (n + 2) =
      ((2 : ℝ) ^ 5 * ((2 : ℝ) ^ 8) ^ (n + 2) * ((n + 2).factorial : ℝ) *
        (((n : ℝ) + 4) ^ 2 / ((n : ℝ) + 3) ^ 5)) * A * E⁻¹ ^ n := by
  have hcanc : E ^ 2 * E⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hE.ne', one_pow]
  have hscale : E ^ 2 * ((2 : ℝ) ^ 8 * E⁻¹) ^ (n + 2) =
      ((2 : ℝ) ^ 8) ^ (n + 2) * E⁻¹ ^ n := by
    rw [mul_pow, pow_add E⁻¹]
    calc
      E ^ 2 * (((2 : ℝ) ^ 8) ^ (n + 2) * (E⁻¹ ^ n * E⁻¹ ^ 2)) =
          (E ^ 2 * E⁻¹ ^ 2) * (((2 : ℝ) ^ 8) ^ (n + 2) * E⁻¹ ^ n) := by ring
      _ = _ := by rw [hcanc, one_mul]
  unfold amnrStreamSpatialEnvelope
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [show ((n : ℝ) + 2) + 2 = (n : ℝ) + 4 by ring,
    show ((n : ℝ) + 2) + 1 = (n : ℝ) + 3 by ring]
  calc
    _ = (E ^ 2 * ((2 : ℝ) ^ 8 * E⁻¹) ^ (n + 2)) *
        ((2 : ℝ) ^ 5 * A * ((n + 2).factorial : ℝ) *
          ((n : ℝ) + 4) ^ 2 / ((n : ℝ) + 3) ^ 5) := by
      field_simp
    _ = _ := by
      rw [hscale]
      ring

/-- Every admissible spatial jet has one constant for the entire budget.
Only abstract real algebra is used in this scale comparison. -/
theorem amnrStreamSpatialEnvelope_le_uniform {A E : ℝ} (hA : 0 ≤ A) (hE : 0 < E)
    {n N : ℕ} (hn : n ≤ N) :
    amnrStreamSpatialEnvelope A E (n + 2) ≤ amnrSpatialVelocityConstant N * A * E⁻¹ ^ n := by
  rw [amnrStreamSpatialEnvelope_gradient hE]
  have hp : ((2 : ℝ) ^ 8) ^ (n + 2) ≤ ((2 : ℝ) ^ 8) ^ (N + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hf : ((n + 2).factorial : ℝ) ≤ ((N + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n + 2 ≤ N + 2)
  have hbase : 1 ≤ (n : ℝ) + 3 := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    linarith only [hn0]
  have hden : 1 ≤ ((n : ℝ) + 3) ^ 5 := one_le_pow₀ hbase
  have hratio : ((n : ℝ) + 4) ^ 2 / ((n : ℝ) + 3) ^ 5 ≤ ((N : ℝ) + 4) ^ 2 := by
    refine (div_le_self (sq_nonneg _) hden).trans ?_
    gcongr
  have hcoef : (2 : ℝ) ^ 5 * ((2 : ℝ) ^ 8) ^ (n + 2) * ((n + 2).factorial : ℝ) *
      (((n : ℝ) + 4) ^ 2 / ((n : ℝ) + 3) ^ 5) ≤ amnrSpatialVelocityConstant N := by
    unfold amnrSpatialVelocityConstant
    gcongr
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hA) (by positivity)

/-- Spatial velocity-gradient jets have a single constant over the entire
source derivative budget. The extra two stream derivatives are checked here. -/
theorem amnr_velocityGradient_spatial_le_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (hbudget : α.length + 2 ≤ AVenhance.Nstar β)
    (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (α.map some)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) z| ≤
      amnrSpatialVelocityConstant (AVenhance.Nstar β) * AVenhance.a β I.Λ m *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hh := (amnr_velocityGradient_spatialWord_raw_of_A3 I hΦ hreg hm α i p z).trans
    (amnrStreamSpatialEnvelope_le_uniform hA.le hE
      (show α.length ≤ AVenhance.Nstar β by omega))
  simpa only [Real.norm_eq_abs] using hh

end AVenhance.Infra.Section4
