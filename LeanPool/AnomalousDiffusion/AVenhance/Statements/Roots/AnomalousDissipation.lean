/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Roots.AnomalousDissipation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Drift.HolderUpgrade

/-! Statement file: `anomalous_dissipation` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- **Theorem 1.1** of Armstrong–Vicol (anomalous dissipation), in dimension 2. For every
`α ∈ (0, 1/3)` there is a divergence-free, `ℤ²`-periodic drift `b` in
`C⁰_t C^{0,α}_x ∩ C^{0,α}_t C⁰_x` on `[0,1] × 𝕋²` and a rate `ϱ` with values in `(0,1]` such that
every mean-zero `H¹` datum satisfies
`limsup_{κ→0⁺} κ ‖∇θ^κ‖²_{L²((0,1)×𝕋²)} ≥ ϱ(‖θ₀‖_{L²}/‖∇θ₀‖_{L²})² ‖θ₀‖²_{L²}`. -/
theorem anomalous_dissipation (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderClass α b ∧ IsContinuousIntoHolder α b ∧ IsDivFree b ∧
      ∃ ϱ : ℝ → ℝ, (∀ r, 0 < ϱ r ∧ ϱ r ≤ 1) ∧
        ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2),
          IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
          ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
            (∀ κ : ℝ, 0 < κ → IsWeakSolutionGrad b κ θ₀ (θ κ) (Dθ κ)) →
            Filter.limsup (fun κ : ℝ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) ≥
              ϱ (Real.sqrt (l2NormSq θ₀) / Real.sqrt (gradNormSq Dθ₀)) ^ 2 * l2NormSq θ₀ := by
  obtain ⟨b, hb, hdiv, hrest⟩ :=
    AVenhance.Proofs.anomalous_dissipation ((α + 1 / 3) / 2) (by linarith) (by linarith)
  exact ⟨b, Infra.Drift.isHolderClass_mono hb hα₀ (by linarith),
    Infra.Drift.isContinuousIntoHolder_of_lt hb hα₀ (by linarith), hdiv, hrest⟩

end AVenhance
