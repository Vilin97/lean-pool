/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.FullAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.SeparatedChainsAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.NoSelectionInputs

/-!
# Proof of the combined main theorem

`anomalous_dissipation_full` is the combined main theorem
(`AVenhance.anomalous_dissipation_full`) without the `IsContinuousIntoHolder` conjunct, which
the public statement derives from it at a larger exponent. It is proved by
    `anomalous_dissipation_full_of_noSelection`
from `noSelection_of_separated`, `separatedChains_of_inputs` and the input contracts.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

open AVenhance

/-- The combined main theorem with the drift class `IsHolderClass`; see
`AVenhance.anomalous_dissipation_full`. -/
theorem anomalous_dissipation_full (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderClass α b ∧ IsDivFree b ∧
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
          ∃ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ₁ t) ≠ l2NormSq (θ₂ t)) :=
  Infra.FullTheorem.anomalous_dissipation_full_of_noSelection
    (fun β C₀ => Infra.FullTheorem.noSelection_of_separated β C₀
      (Infra.FullTheorem.separatedChains_of_inputs β C₀
          (Infra.FullTheorem.Contracts.velGrad_contract β C₀)
        Infra.FullTheorem.Contracts.cosineDatum_contract)) α hα₀ hα₁

end AVenhance.Proofs

end
