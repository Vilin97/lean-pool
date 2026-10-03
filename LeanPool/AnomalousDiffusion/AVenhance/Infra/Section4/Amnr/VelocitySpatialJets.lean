/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialWords

/-! Primitive spatial jets of the actual velocity, extracted from the stream-regularity estimates.
-/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The exact pointwise envelope obtained by undoing the source stream seminorm. -/
def amnrStreamSpatialEnvelope (A E : ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ 5 * A * E ^ 2 * (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) *
    (n.factorial : ℝ) * ((2 : ℝ) ^ 8 * E⁻¹) ^ n / ((n : ℝ) + 1) ^ 2

/-- Every spatial word of length at least two on the actual stream has the
stream-regularity envelope. There is no assumed stream or velocity derivative norm. -/
theorem amnr_stream_spatialWord_raw_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (hα : 2 ≤ α.length) (t : ℝ) (x : Vec 2) :
    ‖amnrSpaceWord α (Φ m t) x‖ ≤
      amnrStreamSpatialEnvelope (AVenhance.a β I.Λ m) (AVenhance.epsilon β I.Λ m) α.length := by
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m)
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
    (AVenhance.streamSeq_isAdmissible hΦ m).1.comp (contDiff_const.prodMk contDiff_id)
  exact amnrSpaceWord_norm_le_of_barNorm hf α (by positivity) (by positivity)
    ((hreg m hm t).2.1 α.length hα) x

/-- The exact envelope for every spatial derivative of the actual velocity
-gradient coefficient. Two additional derivatives fall on the stream. -/
theorem amnr_velocityGradient_spatialWord_raw_of_A3 {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (i p : Fin 2) (z : AmnrSpace) :
    ‖amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (α.map some)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) z‖ ≤
      amnrStreamSpatialEnvelope (AVenhance.a β I.Λ m) (AVenhance.epsilon β I.Λ m) (α.length + 2)
          := by
  have hb := (AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) :=
    contDiffOn_univ.mp (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn i p)
  rw [amnrWord_spatial_slice hB]
  fin_cases i
  · change ‖amnrSpaceWord α
      (fun y => amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (0 : Fin 2) p
        (z.1, y)) z.2‖ ≤ _
    rw [amnrVelocityGradient_stream_zero, amnrSpaceWord_const_smul]
    simp only [Pi.smul_apply, norm_smul]
    simp only [Real.norm_eq_abs, abs_neg, abs_one, one_mul]
    rw [← amnrSpaceWord_append]
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Real.norm_eq_abs] using
      amnr_stream_spatialWord_raw_of_A3 I hΦ hreg hm (α ++ [p, 1]) (by simp) z.1 z.2
  · change ‖amnrSpaceWord α
      (fun y => amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (1 : Fin 2) p
        (z.1, y)) z.2‖ ≤ _
    rw [amnrVelocityGradient_stream_one, ← amnrSpaceWord_append]
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, Real.norm_eq_abs] using
      amnr_stream_spatialWord_raw_of_A3 I hΦ hreg hm (α ++ [p, 0]) (by simp) z.1 z.2

end AVenhance.Infra.Section4
