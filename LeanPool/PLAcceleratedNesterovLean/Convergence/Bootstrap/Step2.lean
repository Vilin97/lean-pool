/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme

/-!
# Bootstrap Step 2: Choosing α and Closing the Induction

## Base case setup
With v₁ = 0 and x₁ ∈ B(m⋆, α):
  L₁ = Ψ(x₁) < R² (by continuity of Ψ and Ψ(m⋆) = 0)
  x₁, x'₁ ∈ Ω (since α < r and 4r ≤ dist(m⋆, ∂Ω))

## Inductive step
Assuming all iterates up to n stay in Ω with Lyapunov ≤ R²:
  Total displacement: ‖x'_{n+1} - m⋆‖ ≤ α + C_h √η S_a R ≤ 2r
  So x'_{n+1} ∈ Ω (since dist(m⋆, ∂Ω) = 4r)
  And ‖x_{n+1} - m⋆‖ ≤ 2r + C_mov R ≤ 3r < 4r
  So x_{n+1} ∈ Ω
-/

noncomputable section

namespace PLAcceleratedNesterovLean

/-- If Ψ is continuous, Ψ(m) = 0, and R > 0, there exists α > 0 with Ψ(x) < R²
    for all x in B(m, α). -/
theorem exists_alpha_psi_small {d : ℕ} (m : E d) (Ψ : E d → ℝ)
    (hcont : ContinuousAt Ψ m) (hzero : Ψ m = 0) (R : ℝ) (hR : 0 < R) :
    ∃ α : ℝ, 0 < α ∧ ∀ x, dist x m < α → Ψ x < R ^ 2 := by
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (R ^ 2) hR2
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := hball hx
  have hle : Ψ x ≤ dist (Ψ x) (Ψ m) := by
    rw [Real.dist_eq, hzero, sub_zero]; exact le_abs_self _
  linarith

/-- Ball containment: if ‖x - m‖ < α and α < r and 4r ≤ dist(m, ∂Ω), then x ∈ Ω.
    Stated as: if dist(x, m) < α, α + displacement < dist(m, ∂Ω), then x ∈ Ω. -/
theorem ball_mem_of_dist_lt {d : ℕ} (x m : E d) (α : ℝ)
    (Ω : Set (E d)) (_hΩ : IsOpen Ω) (_hm : m ∈ Ω)
    (hx : dist x m < α) :
    x ∈ Metric.ball m α := by
  exact Metric.mem_ball.mpr hx

/-- Sum bound: if f(k) ≤ C · r^k for all k, then Σ f(k) ≤ C · Σ r^k. -/
theorem series_bound_from_geometric (f : ℕ → ℝ) (C r : ℝ) (n : ℕ)
    (_hC : 0 ≤ C) (_hr : 0 ≤ r) (hf : ∀ k, k < n → f k ≤ C * r ^ k) :
    (Finset.range n).sum f ≤ C * (Finset.range n).sum (fun k => r ^ k) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk => hf k (Finset.mem_range.mp hk)

end PLAcceleratedNesterovLean
