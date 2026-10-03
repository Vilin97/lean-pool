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
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.SMat

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The forcing `∇ · ((𝐊_m - κ_{m-1} I + 𝐬_{m-1}) ∇T^{(i-1)})` of `e.Tm-1.i` (4036-4040); `∇·(A∇u)`
means `∂_i(A_{ij} ∂_j u)`. -/
def TForcing (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ) (Tprev : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  vecDiv (fun y => (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    I.sMat hΦ m κm t y).mulVec (spaceGrad (Tprev t) y)) x

end Ingredients
end AVenhance
