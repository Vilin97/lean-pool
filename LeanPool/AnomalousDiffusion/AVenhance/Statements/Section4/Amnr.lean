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
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Jcut

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The `3`-tensors `𝐀_{m,n,r}^{ijk}` of `e.A.mnr.def` (4188-4200), `Tm1 = T_{m-1}`, `κm = κ_m`:
`A_{n,0}^{ijk} = -L_{n}(t) ∑_l ξ̂_{m,l} F_l^{ji} ∑_p F_l^{kp} ∂_pT`, where
`F_l = (∇X_{m-1,l})∘X⁻¹_{m-1,l}` (`flowGrad`); the left factor `F_l^{ji}` is the left Jacobian
that replaces the source's `δ_{ij}` (see doc/errata.pdf),
`A_{r+1}^{ijk} = (∂_t + b_{m-1}·∇) A_r^{ijk} - ∂_ℓ b^i_{m-1} A_r^{ℓjk}`.
SIGN OF THE LAST TERM: the source prints `+`; the minus sign is the one for which
`(∂_t + b·∇) ∂_i A^{ijk} = ∂_i A_{r+1}^{ijk}` (checked symbolically, `∇·b = 0`). -/
def Amnr (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (n : ℕ) (Tm1 : ℝ → Vec 2 → ℝ) :
    ℕ → ℝ → Vec 2 → Fin 2 → Fin 2 → Fin 2 → ℝ
  | 0 => fun t x i j k =>
      -I.LMN κm m n t *
        ∑' l : ℤ, I.hatXiML m l t * (I.flowGrad hΦ m l t x j i *
          ∑ p : Fin 2, I.flowGrad hΦ m l t x k p * spaceGrad (Tm1 t) x p)
  | r + 1 => fun t x i j k =>
      (deriv (fun s => Amnr hΦ m κm n Tm1 r s x i j k) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (fun y => Amnr hΦ m κm n Tm1 r t y i j k) x)) -
      ∑ ℓ : Fin 2, spaceGrad (fun y => streamVel (Φ (m - 1)) t y i) x ℓ *
        Amnr hΦ m κm n Tm1 r t x ℓ j k

end Ingredients
end AVenhance
