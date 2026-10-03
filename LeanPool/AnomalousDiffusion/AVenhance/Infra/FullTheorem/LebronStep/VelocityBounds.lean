/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.DivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitSeries
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity

/-! # Uniform velocity bound and Lemma-U hypotheses for the stream drifts (Lemma r.LeBron, step (b))

`‖streamVel (Φ j) t x‖ ≤ B(β)` uniformly in `j`, `t`, `x` and in the ingredients (only `Λ ≥ 2^7`
is used), from stream-regularity (`stream_regularity`) and the geometric decay of `ε_j^{β-1}`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance AVenhance.Infra.Construction

/-- The uniform velocity bound `B(β) = 320 / (1 - 128^{-(β-1)})`. -/
def velBound (β : ℝ) : ℝ := 320 / (1 - (128 : ℝ) ^ (-(β - 1)))

theorem velBound_nonneg {β : ℝ} (hβ : 1 < β) : 0 ≤ velBound β := by
  unfold velBound
  have hs : 0 < β - 1 := by linarith
  have h1 : (128 : ℝ) ^ (-(β - 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_nonneg (by norm_num) (by linarith)

/-- Components of `σ v` are `∓` components of `v`. -/
theorem VelocityBounds.norm_sigma_mulVec_le (v : Vec 2) : ‖sigmaMat.mulVec v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => ?_
  fin_cases i
  · simp only [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simpa using norm_le_pi_norm v 1
  · simp only [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simpa using norm_le_pi_norm v 0

theorem VelocityBounds.streamSlice_contDiff {Ψ : ℝ → Vec 2 → ℝ} (hΨ : IsAdmissibleStream Ψ) (t :
    ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Ψ t) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  exact hΨ.1.comp hmap

/-- Increment of the gradient of consecutive streams. -/
theorem VelocityBounds.spaceGrad_increment_le {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (t : ℝ) (x : Vec 2) :
    ‖spaceGrad (Φ m t) x - spaceGrad (Φ (m - 1) t) x‖ ≤ 320 * epsilon β I.Λ m ^ (β - 1) := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hB : 0 ≤ 320 * epsilon β I.Λ m ^ (β - 1) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg he.le _)
  refine (pi_norm_le_iff_of_nonneg hB).2 fun i => ?_
  have hc := streamIncrement_deriv_coordinate_le hseq hreg hm t x i
  have hd1 := (VelocityBounds.streamSlice_contDiff (streamSeq_isAdmissible hseq m)
      t).differentiable (by simp) x
  have hd2 := (VelocityBounds.streamSlice_contDiff (streamSeq_isAdmissible hseq (m - 1))
      t).differentiable
    (by simp) x
  have h := fderiv_sub hd1 hd2
  rw [h] at hc
  simpa [spaceGrad] using hc

/-- Partial sums of the gradient. -/
theorem VelocityBounds.spaceGrad_partial_le {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) (t : ℝ) (x : Vec 2)
    (j : ℕ) :
    ‖spaceGrad (Φ j t) x‖ ≤ 320 * ∑ k ∈ Finset.range j, epsilon β I.Λ (1 + k) ^ (β - 1) := by
  induction j with
  | zero =>
    have h0 : Φ 0 t = fun _ => 0 := by rw [hseq.1]
    have h00 : spaceGrad (Φ 0 t) x = 0 := by
      rw [h0]; ext i; simp [spaceGrad]
    simp [h00]
  | succ j ih =>
    have hinc := VelocityBounds.spaceGrad_increment_le hseq hreg (m := j + 1) (by omega) t x
    simp only [Nat.add_sub_cancel] at hinc
    rw [Finset.sum_range_succ, mul_add]
    calc ‖spaceGrad (Φ (j + 1) t) x‖
        ≤ ‖spaceGrad (Φ j t) x‖ + ‖spaceGrad (Φ (j + 1) t) x - spaceGrad (Φ j t) x‖ := by
          have := norm_add_le (spaceGrad (Φ j t) x)
            (spaceGrad (Φ (j + 1) t) x - spaceGrad (Φ j t) x)
          simpa using this
      _ ≤ _ := by
          have e : epsilon β I.Λ (j + 1) = epsilon β I.Λ (1 + j) := by rw [Nat.add_comm]
          rw [e] at hinc
          linarith

/-- **Uniform bound on the stream velocities.** -/
theorem streamVel_norm_le {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (j : ℕ) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ j) t x‖ ≤ velBound β := by
  obtain ⟨C, -, hC⟩ := stream_regularity β
  have hreg : StreamRegularityBounds C I Φ := fun m hm t => hC I Φ hseq m hm t
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hΛ : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
  have hsum := epsilon_rpow_sum_bound I hs 1 j
  have he1 : epsilon β I.Λ 1 ^ (β - 1) ≤ 1 :=
    Real.rpow_le_one (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le (Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
        I.two_pow_seven_le) hs.le
  have hden : (1 : ℝ) - (128 : ℝ) ^ (-(β - 1)) ≤ 1 - (I.Λ : ℝ) ^ (-(β - 1)) := by
    have : (I.Λ : ℝ) ^ (-(β - 1)) ≤ (128 : ℝ) ^ (-(β - 1)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hΛ hs.le)
    linarith
  have hden0 : 0 < (1 : ℝ) - (128 : ℝ) ^ (-(β - 1)) := by
    have h1 : (128 : ℝ) ^ (-(β - 1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hsum' : ∑ k ∈ Finset.range j, epsilon β I.Λ (1 + k) ^ (β - 1) ≤
      1 / (1 - (128 : ℝ) ^ (-(β - 1))) := by
    refine hsum.trans ?_
    calc epsilon β I.Λ 1 ^ (β - 1) / (1 - (I.Λ : ℝ) ^ (-(β - 1)))
        ≤ 1 / (1 - (I.Λ : ℝ) ^ (-(β - 1))) :=
          div_le_div_of_nonneg_right he1 (by linarith)
      _ ≤ 1 / (1 - (128 : ℝ) ^ (-(β - 1))) :=
          one_div_le_one_div_of_le hden0 hden
  calc ‖streamVel (Φ j) t x‖ ≤ ‖spaceGrad (Φ j t) x‖ := VelocityBounds.norm_sigma_mulVec_le _
    _ ≤ 320 * ∑ k ∈ Finset.range j, epsilon β I.Λ (1 + k) ^ (β - 1) :=
        VelocityBounds.spaceGrad_partial_le hseq hreg t x j
    _ ≤ 320 * (1 / (1 - (128 : ℝ) ^ (-(β - 1)))) := by gcongr
    _ = velBound β := by unfold velBound; ring

/-- Spatial periodicity of the finite stream velocities. -/
theorem streamVel_isZ2Periodic {Ψ : ℝ → Vec 2 → ℝ} (hΨ : IsAdmissibleStream Ψ) (t : ℝ) :
    IsZ2Periodic (streamVel Ψ t) := by
  intro n x
  have hb := Classical.streamVel_smoothPeriodic Ψ hΨ
  simpa using hb.periodic 0 n t x

end AVenhance.Infra.FullTheorem
