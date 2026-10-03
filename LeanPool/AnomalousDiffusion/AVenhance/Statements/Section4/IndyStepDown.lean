/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelLipschitz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Flux
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.TimeAvgMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.GradMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.XiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Ansatz
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Section4.IndyStepDown

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Step-down estimate: `p.indystepdown` (8026-8062).  Binder order and constants as in
    `bigbound`.  Conclusions:
`e.homogenization.m` (for every `t ∈ [0,1]`, the `L^∞_tL²_x` norm plus the
    `κ_m^{1/2}‖∇·‖_{L²_{t,x}}`
term, `∇θ_m` and `∇θTilde_m` the classical gradients) and `e.tildethetam.energy.diss` in
    cross-multiplied
form `|κ_m D_m - κ_{m-1} D_{m-1}| ≤ Cε_{m-1}^δ κ_{m-1} D_{m-1}`, `D_j = ‖∇θ_j‖²_{L²((0,1)×𝕋²)}`
(equal to the printed ratio bound when `D_{m-1} > 0`, and true, rather than `0/0`, for `θ₀ = 0`).
Conjunct (ii) is asserted only for `6/5 ≤ β` and at later levels `ε_{m-1}^{1+γ/2-δ} ≤ R`. -/
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
            (I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))) := by
  exact AVenhance.Proofs.indystepdown β C₀

end AVenhance
