/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.GenLocalArgument
import LeanPool.PLAcceleratedNesterovLean.Convergence.PhaseSchedule
import LeanPool.PLAcceleratedNesterovLean.Convergence.RateArithmetic
import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Step1

/-!
# Helpers for single-phase convergence proof

Helper lemmas for the local convergence argument, covering initial Lyapunov
bounds and phase transitions.

## Lemmas provided

1. `lyapunov_initial_bound` — Lyap(x₀, v=0) ≤ C·dist² for L-smooth f
2. `gen_at_every_phase` — gen theorem at any m ∈ S for any phase k ≥ 1
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold Finset


/-! ## 1. Initial Lyapunov bound -/

/-- For L-smooth f with ∇f(m)=0, the initial state (x₀, v=0) has Lyapunov
    bounded by C·dist(x₀,m)². Uses that f(x₀)-f* ≤ Lyap and
    ‖x₀-π(x₀)‖ ≤ dist(x₀,m). -/
theorem lyapunov_initial_bound
    {d : ℕ}
    (P : E d →L[ℝ] E d) (μ' : ℝ) (hμ' : 0 < μ')
    (π : E d → E d) (f : E d → ℝ)
    (η : ℝ) (_hη_pos : 0 < η)
    (_hμη : μ' * η < 1)
    (hbdd : BddBelow (Set.range f))
    -- P is a bounded projection
    (_hP_norm : ∀ v : E d, ‖P v‖ ≤ ‖v‖)
    -- m is a minimizer, π maps to minimizers
    (m : E d) (hm : m ∈ argminSet f)
    (_hπ_in_S : ∀ x, π x ∈ argminSet f)
    -- π is distance-non-increasing: dist(x, π(x)) ≤ dist(x, m) for m ∈ S
    (hπ_near : ∀ x : E d, dist x (π x) ≤ dist x m)
    -- Upper bound on f(x₀) - f(m) ≤ C_f · dist(x₀,m)²
    (C_f : ℝ) (_hC_f : 0 < C_f)
    (hf_bound : ∀ x₀ : E d, f x₀ - f m ≤ C_f * dist x₀ m ^ 2)
    (x₀ : E d) :
    lyapunovOfState P μ' π f η ⟨x₀, 0⟩ ≤ (C_f + μ' / 2) * dist x₀ m ^ 2 := by
  simp only [lyapunovOfState, auxVarOfState, normalDispOfState,
    NesterovState.lookahead]
  -- v = 0 simplifications
  simp only [smul_zero, add_zero, map_zero, sub_zero]
  -- Goal: (f x₀ - fStar f) + ‖√μ' • (x₀ - π x₀)‖²/2 + λ·‖0‖² ≤ (C_f + μ'/2)·dist²
  have h_gap : f x₀ - fStar f ≤ C_f * dist x₀ m ^ 2 := by
    have hfm : fStar f = f m := by
      apply le_antisymm
      · exact ciInf_le hbdd m
      · exact le_ciInf fun y => hm y
    rw [hfm]; exact hf_bound x₀
  have h_norm_e : ‖x₀ - π x₀‖ ≤ dist x₀ m := by
    calc ‖x₀ - π x₀‖ = dist x₀ (π x₀) := (dist_eq_norm x₀ (π x₀)).symm
      _ ≤ dist x₀ m := hπ_near x₀
  have h_u_sq :
      ‖Real.sqrt μ' • (x₀ - π x₀)‖ ^ 2 / 2 ≤ μ' / 2 * dist x₀ m ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have := Real.sq_sqrt (le_of_lt hμ')
    nlinarith [sq_nonneg (Real.sqrt μ'), sq_nonneg ‖x₀ - π x₀‖,
               sq_nonneg (dist x₀ m), sq_abs (Real.sqrt μ' * ‖x₀ - π x₀‖),
               mul_le_mul_of_nonneg_left
                 (sq_le_sq' (by linarith [norm_nonneg (x₀ - π x₀), h_norm_e])
                   h_norm_e)
                 (le_of_lt hμ')]
  -- The λ·‖P 0‖² term is 0
  have h_Pv_zero : ‖(0 : E d)‖ ^ 2 = 0 := by simp
  have h_norm_simpl : ‖(0 : E d) + Real.sqrt μ' • (x₀ - π x₀)‖ = ‖Real.sqrt μ' • (x₀ - π x₀)‖ := by
    rw [zero_add]
  rw [h_Pv_zero, mul_zero, add_zero, h_norm_simpl]
  linarith

/-! ## 2. Gen theorem at arbitrary phase and base point -/

/-- The gen theorem works at any m ∈ S for any phase k ≥ 1.
    This is just `local_convergence_at_base_point_gen` applied with phase-k parameters.
    Also exports C_coer, projector properties, and coercivity bound. -/
theorem gen_at_every_phase
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ) (hμ_le_L : μ ≤ ↑L)
    (f : E d → ℝ) (S : Set (E d)) (hrange : S = argminSet f)
    (U : Set (E d))
    (hTub : IsTubularNeighborhoodOfSubmanifold S U)
    (hPL : PolyakLojasiewicz f μ U)
    (hC2 : ContDiffOn ℝ 2 f U)
    (hLip : LipschitzOnWith ↑L (gradient f) U)
    (π : E d → E d)
    (hπ_on_U : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (hπ_fix : ∀ x ∈ S, π x = x)
    (hπ_in_S : ∀ x, π x ∈ S)
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (m : E d) (hm : m ∈ S)
    (k : ℕ) (hk : 1 ≤ k) :
    let η := 1 / (L : ℝ)
    let P := fderiv ℝ π m
    let ρ_gen := (1 - Real.sqrt (muOfPhase μ k * η)) / (1 + Real.sqrt (muOfPhase μ k * η))
    ∃ (Ω : Set (E d)) (δ r_ball C_coer : ℝ),
      IsOpen Ω ∧ m ∈ Ω ∧ Ω ⊆ U ∧ 0 < δ ∧ 0 < r_ball ∧ 0 < C_coer ∧
      Metric.ball m r_ball ⊆ Ω ∧
      (∀ x : E d, P (P x) = P x) ∧
      (∀ v : E d, ‖P v‖ ≤ ‖v‖) ∧
      muOfPhase μ k * η < 1 ∧
      (∀ s : NesterovState d, s.x ∈ Ω → s.lookahead η ∈ Ω →
        ‖s.v‖ ^ 2 + muOfPhase μ k * ‖normalDispOfState π η s‖ ^ 2 ≤
          C_coer * lyapunovOfState P (muOfPhase μ k) π f η s) ∧
      ∀ s₀ : NesterovState d,
        s₀.x ∈ Metric.ball m δ →
        s₀.lookahead η ∈ Metric.ball m δ →
        lyapunovOfState P (muOfPhase μ k) π f η s₀ ≤ δ ^ 2 →
        (∀ j : ℕ,
          (nesterovSeqGen f η ρ_gen s₀ j).x ∈ Ω ∧
          (nesterovSeqGen f η ρ_gen s₀ j).lookahead η ∈ Ω) ∧
        (∀ j : ℕ,
          (nesterovSeqGen f η ρ_gen s₀ j).x ∈ Metric.ball m r_ball ∧
          (nesterovSeqGen f η ρ_gen s₀ j).lookahead η ∈ Metric.ball m r_ball) ∧
        (∀ j : ℕ,
          lyapunovOfState P (muOfPhase μ k) π f η (nesterovSeqGen f η ρ_gen s₀ (j + 1)) ≤
            (1 - (1 - thetaOfPhase k) * Real.sqrt (muOfPhase μ k * η)) ^ (j + 1) *
            lyapunovOfState P (muOfPhase μ k) π f η s₀) ∧
        (∀ j : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          π ((nesterovSeqGen f η ρ_gen s₀ j).lookahead η) +
            t • ((nesterovSeqGen f η ρ_gen s₀ j).lookahead η -
                  π ((nesterovSeqGen f η ρ_gen s₀ j).lookahead η)) ∈ U) :=
  local_convergence_at_base_point_gen hd L hL μ hμ hμ_le_L
    (muOfPhase μ k) (muOfPhase_pos hμ hk) (muOfPhase_lt_mu hμ k)
    (thetaOfPhase k) (thetaOfPhase_pos k) (thetaOfPhase_lt_one hk)
    f S hrange U hTub hPL hC2 hLip π hπ_on_U hπ_fix hπ_in_S hgrad_zero m hm

end PLAcceleratedNesterovLean
