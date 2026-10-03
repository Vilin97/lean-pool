/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.Statements
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.LemmaUContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.KappaBounds

/-! # Named forms of the statements used (analytic case of `r.LeBron.2`)

`LemmaUWith CU`, `LebronWith β C₀ μ C`, `WindowWith β C₀ c₁ Λ₁` are the bodies of
`LemmaUContract`, `LebronStepStatement`, `kappaSeq_window` with the constants as parameters, so
that helper lemmas can take them as hypotheses. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Body of `LemmaUContract` with the constant a parameter. -/
def LemmaUWith (CU : ℝ) : Prop :=
    ∀ b : ℝ → Vec 2 → Vec 2,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)) → IsDivFree b →
    ∀ B : ℝ, 0 ≤ B → (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B) →
    ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
    ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2), IsPeriodicH1With θ₀ Dθ₀ →
    ∀ (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2), IsWeakSolutionGrad b κ θ₀ θ Dθ →
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤
        CU * (1 + B) / Real.sqrt κ * |t - s| ^ ((1 : ℝ) / 4) *
          Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀)

theorem lemmaU_with_of_contract (h : LemmaUContract) : ∃ CU : ℝ, 0 < CU ∧ LemmaUWith CU := h

/-- Body of `LebronStepStatement` with the constants as parameters. -/
def LebronWith (β C₀ μ C : ℝ) : Prop :=
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
          (fun t x => θm t x - θprev t x)

theorem lebron_with_of_statement {β C₀ : ℝ} (h : LebronStepStatement β C₀) :
    ∃ μ C : ℝ, 0 < μ ∧ LebronWith β C₀ μ C := h

/-- Body of `kappaSeq_window` with the constants as parameters. -/
def WindowWith (β C₀ c₁ Λ₁ : ℝ) : Prop :=
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₁ ≤ (I.Λ : ℝ) → ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ j : ℕ, (j = m - 1 ∨ j = m) →
        c₁ * epsilon β I.Λ (m - 1) ^ lebronP β ≤ I.kappaSeq κ M j ∧ I.kappaSeq κ M j ≤ 1

theorem window_with (β C₀ : ℝ) : ∃ c₁ Λ₁ : ℝ, 0 < c₁ ∧ WindowWith β C₀ c₁ Λ₁ :=
  kappaSeq_window β C₀

end AVenhance.Infra.FullTheorem
