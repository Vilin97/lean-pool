/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
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
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Literal restatements of the main theorem, classical well-posedness and stream-function
    estimates statements

Each `…Statement` is the proposition of the corresponding public statement, restated
(theorem binders turned into `∀` binders; hypothesis binder names that the body does not
mention carry a `_` prefix to satisfy the unused-variable linter — alpha-equivalent, so `exact`
    applies), so that `anomalous_dissipation_of_keystones` can be
closed by `exact` once the three estimates are proved.  The statement files themselves are never
    imported. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- The main theorem with the drift class `IsHolderClass` only, its binders as `∀`. The public
statement `AVenhance.anomalous_dissipation` adds `IsContinuousIntoHolder`, obtained from this one
at a larger exponent by `Infra.Drift.isContinuousIntoHolder_of_lt`. -/
def AnomalousDissipationStatement : Prop :=
  ∀ (α : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3),
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderClass α b ∧ IsDivFree b ∧
      ∃ ϱ : ℝ → ℝ, (∀ r, 0 < ϱ r ∧ ϱ r ≤ 1) ∧
        ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2),
          IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
          ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
            (∀ κ : ℝ, 0 < κ → IsWeakSolutionGrad b κ θ₀ (θ κ) (Dθ κ)) →
            Filter.limsup (fun κ : ℝ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) ≥
              ϱ (Real.sqrt (l2NormSq θ₀) / Real.sqrt (gradNormSq Dθ₀)) ^ 2 * l2NormSq θ₀

/-- Verbatim proposition of the public statement `AVenhance.classical_wellposed` (classical
    well-posedness), its binders as `∀`. -/
def ClassicalWellposedStatement : Prop :=
  ∀ (φ : ℝ → Vec 2 → ℝ) (_hφ : IsAdmissibleStream φ) (κ : ℝ) (_hκ : 0 < κ)
    (F : ℝ → Vec 2 → ℝ)
    (_hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (_hFper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (_hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (_hper : IsZ2Periodic θ₀),
    ∃ θ : ℝ → Vec 2 → ℝ, IsClassicalSol (streamVel φ) κ F θ₀ θ ∧
      ∀ θ' : ℝ → Vec 2 → ℝ, IsClassicalSol (streamVel φ) κ F θ₀ θ' →
        ∀ t : ℝ, 0 ≤ t → ∀ x, θ' t x = θ t x

/-- Verbatim proposition of the public statement `AVenhance.limit_field_regular` (stream-function
    estimates). -/
def LimitFieldRegularStatement (β : ℝ) : Prop :=
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ →
        ∃ φ : ℝ → Vec 2 → ℝ,
          (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
          (∀ (M : ℕ) (t : ℝ) (x : Vec 2), |φ t x - Φ M t x| ≤ C * epsilon β I.Λ (M + 1) ^ β) ∧
          (∀ t, Differentiable ℝ (φ t)) ∧
          TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
            (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) atTop
            (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
          ∀ α : ℝ, 0 < α → α < β - 1 → IsHolderClass α (streamVel φ) ∧ IsDivFree (streamVel φ)

end AVenhance.Infra.Section5.Integration
