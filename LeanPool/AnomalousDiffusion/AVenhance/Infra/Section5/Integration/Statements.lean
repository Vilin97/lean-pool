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

/-! # Literal restatements of the big-bound estimate / step-down part (i) statement bodies

`BigBoundStatement β C₀` is the proposition of the public statement
`AVenhance.bigbound` (Section4/BigBound.lean), and `IndyStepDownPartIStatement β C₀` is the
Step-down estimate `AVenhance.indystepdown` (Section4/IndyStepDown.lean) with its conclusion
restricted to conjunct (i) (`e.homogenization.m`); conjunct (ii) is not stated here.  The
    statement modules themselves may not be imported; the proof
body can be replaced by `exact <wiring theorem> …`, which checks the restatement by definitional
    unfolding. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- The proposition of the big-bound estimate `AVenhance.bigbound β C₀` (restated). -/
def BigBoundStatement (β : ℝ) (C₀ : ℝ) : Prop :=
    ∃ C : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
        ENNReal.ofReal (I.kappaSeq κ M m ^ (-(1 / 2 : ℝ))) *
            (∫⁻ t in Set.Ioo (0 : ℝ) 1,
              hMinusOneNorm (fun x => advDiffOp (streamVel (Φ m)) (I.kappaSeq κ M m)
                (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β))) t x) ^ 2) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀))

/-- The step-down estimate `AVenhance.indystepdown β C₀` with the conclusion cut down to conjunct
    (i)
(`e.homogenization.m`); premises as in the statement. -/
def IndyStepDownPartIStatement (β : ℝ) (C₀ : ℝ) : Prop :=
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
          C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀))

/-- The proposition of the step-down `AVenhance.indystepdown β C₀` (conjunct (ii) gated by `6/5 ≤
    β` and the later scale condition), restated.  Used as an explicit,
distinctly named hypothesis by the main-theorem assembly; the statement file itself is never
    imported. -/
def IndyStepDownStatement (β : ℝ) (C₀ : ℝ) : Prop :=
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
            (I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))

end AVenhance.Infra.Section5.Integration
