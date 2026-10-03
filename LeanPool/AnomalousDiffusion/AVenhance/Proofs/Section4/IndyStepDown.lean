/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A8Provider
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmPiolaRateFamily

/-! Proof of the step-down estimate (`AVenhance.indystepdown`).

The statement below is identical to the one (copied from
`AVenhance/Section4/IndyStepDown.lean`); the statement file is not imported. The proof is
`Infra.Section5.Contracts.indystepdown_of_piolaRate` fed with the Piola-source rate
`hmPiolaSourceRate_onA7`: part (i) (big-bound estimate plus part I) and part (ii) (relative step)
    from the three leaves
— HTilde sup, the Section 4 iterate and the S-amplitude
trace — every other input being produced. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Proofs

/-- Step-down proof. Its statement is identical to `AVenhance.indystepdown`. -/
theorem indystepdown (β : ℝ) (C₀ : ℝ) :
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ (θm θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) +
            Real.sqrt (I.kappaSeq κ M m) *
              Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x -
                spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
          C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)) ∧
        ((6 : ℝ) / 5 ≤ β →
          epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        |I.kappaSeq κ M m * spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x) -
            I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)| ≤
          C * epsilon β I.Λ (m - 1) ^ delta β *
            (I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))) :=
  Infra.Section5.Contracts.indystepdown_of_piolaRate β C₀
    (Infra.Section5.Contracts.hmPiolaSourceRate_onA7 β C₀)

end AVenhance.Proofs

end
