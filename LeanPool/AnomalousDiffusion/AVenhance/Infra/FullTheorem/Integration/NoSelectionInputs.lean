/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.SeparationContract

/-! # small inputs of the no-selection argument

* `TwoDiffusivityContract`: classical solutions with the same drift and two diffusivities
  stay close in `L²` on `[0,1]`;
* `CosineDatumContract`: facts about the cosine data `c cos (2π n x₀)`;
* `VelGradContract`: the gradient of the stream-sequence drift is `O(ε_m^{β-2})`;
* `A0CoreContract`: the ingredient-level form of the main theorem for the limit field of one
    stream sequence. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Same drift, two diffusivities: the `L²` distance on `[0,1]` is `|κ-κ'|/(2√(κκ')) ‖θ₀‖`. -/
def TwoDiffusivityContract : Prop :=
  ∀ Ψ : ℝ → Vec 2 → ℝ, IsAdmissibleStream Ψ →
  ∀ κ κ' : ℝ, 0 < κ → 0 < κ' →
  ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ →
  ∀ θ θ' : ℝ → Vec 2 → ℝ,
    IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ →
    IsClassicalSol (streamVel Ψ) κ' (fun _ _ => 0) θ₀ θ' →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ t x - θ' t x)) ≤
        |κ - κ'| / (2 * Real.sqrt (κ * κ')) * Real.sqrt (l2NormSq θ₀)

/-- Facts about the cosine data. -/
def CosineDatumContract : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : ℝ,
    let θ₀ : Vec 2 → ℝ := fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)
    let lam : ℝ := 4 * Real.pi ^ 2 * (n : ℝ) ^ 2
    ContDiff ℝ (⊤ : ℕ∞) θ₀ ∧ IsZ2Periodic θ₀ ∧ MeanZeroOn unitCube θ₀ ∧
    l2NormSq θ₀ = c ^ 2 / 2 ∧
    IsPeriodicH1With θ₀ (spaceGrad θ₀) ∧
    gradNormSq (spaceGrad θ₀) = lam * l2NormSq θ₀ ∧
    hessNormSq θ₀ ≤ lam * gradNormSq (spaceGrad θ₀) ∧
    IsThetaAnalytic (1 / (2 * Real.pi * (n : ℝ))) θ₀

/-- Gradient bound for the drift of the stream sequence. -/
def VelGradContract (β C₀ : ℝ) : Prop :=
  ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ I : Ingredients β,
    I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
    ∀ Φ, IsStreamSeq I Φ → ∀ m : ℕ, 1 ≤ m → ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ x, ∀ i j : Fin 2,
      |spaceGrad (fun y => streamVel (Φ m) t y i) x j| ≤ Cb * epsilon β I.Λ m ^ (β - 2)

/-- The main theorem at ingredient level, for the limit field of one stream sequence (for `6/5 ≤
    β`). -/
def A0CoreContract (β C₀ : ℝ) : Prop :=
  ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₀ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
    ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
    ∃ ϱ : ℝ → ℝ, (∀ r, 0 < ϱ r ∧ ϱ r ≤ 1) ∧
      ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2),
        IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
        ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
          (∀ κ : ℝ, 0 < κ → IsWeakSolutionGrad (streamVel φ) κ θ₀ (θ κ) (Dθ κ)) →
          Filter.limsup (fun κ : ℝ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) ≥
            ϱ (Real.sqrt (l2NormSq θ₀) / Real.sqrt (gradNormSq Dθ₀)) ^ 2 * l2NormSq θ₀

end AVenhance.Infra.FullTheorem
