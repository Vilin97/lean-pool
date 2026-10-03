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
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.HMinusOneNorm

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `e.theta0.anal` (3835-3838) = `e.theta0.anal.encore` (8030-8035): with `‖∇ⁿ f‖_X := max_{|α|=n}
‖∂^α f‖_X` (`e.nabla.n`, 944) the two displays coincide.  The maximum over multi-indices is
expressed as a bound for every ordered coordinate tuple `i : Fin n → Fin 2` (as in `barNorm`; equal
for `C^n` functions by symmetry of the derivative), for every `n ∈ ℕ = {1,2,…}`. -/
def IsThetaAnalytic (R : ℝ) (θ₀ : Vec 2 → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ i : Fin n → Fin 2,
    Real.sqrt (∫ x in unitCube, (iteratedFDeriv ℝ n θ₀ x (fun j => basisVec (i j))) ^ 2) ≤
      Real.sqrt (l2NormSq θ₀) * ((n.factorial : ℝ) / R ^ n)

end AVenhance
