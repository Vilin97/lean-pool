/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsTestFunction
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsHolderTimeL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.HolderTimeL2Le
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsTransportWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.FullTheorem.AnomalousDissipationFull
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Drift.HolderUpgrade

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance
/-- **The combined main theorem.** For every `α ∈ (0, 1/3)` there is one divergence-free,
`ℤ²`-periodic drift `b` in `C⁰_t C^{0,α}_x ∩ C^{0,α}_t C⁰_x` on `[0,1] × 𝕋²` such that:
(i) anomalous dissipation (Theorem 1.1 of Armstrong–Vicol) holds for every mean-zero `H¹` datum,
  with a rate `ϱ` depending only on `‖θ₀‖_{L²}/‖∇θ₀‖_{L²}`;
(ii) uniform time regularity (Remark r.LeBron.2): for every `κ ∈ 𝒦 = ⋃_j [κ_j/2, 2κ_j]`, where
  `κ_j → 0` and `4κ_{j+1} < κ_j`, every solution satisfies
  `‖θ^κ‖_{C^{0,μ}([0,1];L²)} ≤ C‖θ₀‖_{H¹}`;
(iii) non-uniqueness of vanishing-diffusivity limits (a corrected form of Proposition
  p.no.selection.principle): there is a class `𝒟` of smooth, mean-zero, nonzero data, closed under
  nonzero scalings and containing `cos(2πn x₁)` for infinitely many `n`, such that for every
  `θ₀ ∈ 𝒟` the solutions along `κ_{2j}/2` and along `2κ_{2j}` converge in `C^{0,ν}([0,1];L²)` to
  two weak solutions of the transport equation whose `L²` norms differ at some time. -/
theorem anomalous_dissipation_full (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderClass α b ∧ IsContinuousIntoHolder α b ∧ IsDivFree b ∧
    ∃ ϱ : ℝ → ℝ, (∀ r, 0 < ϱ r ∧ ϱ r ≤ 1) ∧
    ∃ κseq : ℕ → ℝ, (∀ j, 0 < κseq j) ∧ (∀ j, 4 * κseq (j + 1) < κseq j) ∧
      Tendsto κseq atTop (𝓝 0) ∧
    ∃ μ ν C : ℝ, 0 < μ ∧ 0 < ν ∧
    ∃ 𝒟 : Set (Vec 2 → ℝ),
      -- (i) anomalous dissipation (main theorem's conclusion)
      (∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2),
        IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
        ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
          (∀ κ : ℝ, 0 < κ → IsWeakSolutionGrad b κ θ₀ (θ κ) (Dθ κ)) →
          Filter.limsup (fun κ : ℝ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) ≥
            ϱ (Real.sqrt (l2NormSq θ₀) / Real.sqrt (gradNormSq Dθ₀)) ^ 2 * l2NormSq θ₀) ∧
      -- (ii) uniform time regularity along 𝒦
      (∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2),
        IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
        ∀ κ ∈ ⋃ j : ℕ, Set.Icc (κseq j / 2) (2 * κseq j),
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolution b κ θ₀ θ →
          HolderTimeL2Le μ (C * Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀)) θ) ∧
      -- (iii) no selection: the data class
      (∀ θ₀ ∈ 𝒟, ContDiff ℝ (⊤ : ℕ∞) θ₀ ∧ IsZ2Periodic θ₀ ∧ MeanZeroOn unitCube θ₀ ∧
        0 < l2NormSq θ₀) ∧
      (∀ θ₀ ∈ 𝒟, ∀ c : ℝ, c ≠ 0 → (fun x => c * θ₀ x) ∈ 𝒟) ∧
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        (fun x : Vec 2 => Real.cos (2 * Real.pi * (n : ℝ) * x 0)) ∈ 𝒟) ∧
      -- (iii) no selection: two distinct vanishing-diffusivity limits
      (∀ θ₀ ∈ 𝒟, ∀ θ : ℝ → ℝ → Vec 2 → ℝ,
        (∀ κ : ℝ, 0 < κ → IsWeakSolution b κ θ₀ (θ κ)) →
        ∃ θ₁ θ₂ : ℝ → Vec 2 → ℝ,
          IsTransportWeakSolution b θ₀ θ₁ ∧ IsTransportWeakSolution b θ₀ θ₂ ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
            HolderTimeL2Le ν η (fun t x => θ (κseq (2 * j) / 2) t x - θ₁ t x)) ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
            HolderTimeL2Le ν η (fun t x => θ (2 * κseq (2 * j)) t x - θ₂ t x)) ∧
          ∃ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ₁ t) ≠ l2NormSq (θ₂ t)) := by
  obtain ⟨b, hb, hdiv, hrest⟩ :=
    AVenhance.Proofs.anomalous_dissipation_full ((α + 1 / 3) / 2) (by linarith) (by linarith)
  exact ⟨b, Infra.Drift.isHolderClass_mono hb hα₀ (by linarith),
    Infra.Drift.isContinuousIntoHolder_of_lt hb hα₀ (by linarith), hdiv, hrest⟩

end AVenhance
