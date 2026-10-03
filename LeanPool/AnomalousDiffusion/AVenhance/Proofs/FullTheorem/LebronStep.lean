/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.LebronStepAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.LemmaU

/-!
# Lemma r.LeBron proof

`lebron_step` is the proof of Lemma r.LeBron (`AVenhance.lebron_step`): its statement is
identical to the one (the statement file is not imported), and it is proved from the
Lemma U contract by `Infra.FullTheorem.lebron_step_of_lemmaU`.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

open AVenhance

/-- Lemma r.LeBron proof. Its statement is identical to `AVenhance.lebron_step`. -/
theorem lebron_step (β : ℝ) (C₀ : ℝ) :
    ∃ μ C : ℝ, 0 < μ ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ θm θprev : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        HolderTimeL2Le μ
          (C * epsilon β I.Λ (m - 1) ^ (delta β / 2) *
            Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)))
          (fun t x => θm t x - θprev t x) :=
  Infra.FullTheorem.lebron_step_of_lemmaU Infra.FullTheorem.Contracts.lemmaU_contract β C₀

end AVenhance.Proofs

end
