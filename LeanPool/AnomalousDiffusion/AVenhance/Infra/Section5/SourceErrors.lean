/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.JHat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Amnr

/-! The two source error fields appearing in the Section 5.1 residual. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The `d_m` field, the corrected formulation (9) and §9.4 (convention):
`Σ_l ξ̂_l F_lᵀ (JHat - 𝒥) F_l ∇T` plus the terminal `A_{m,n,Jcut} q_{m,n,Jcut}` tail. -/
def sourceErrorD (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  (∑' l : ℤ, I.hatXiML m l t •
    ((I.flowGrad hΦ m l t x).transpose.mulVec
      ((I.Jhat κm m t - I.flux κm m t).mulVec
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))) +
    (fun i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n T (Jcut β) t x i j k *
        I.qMNR κm m n (Jcut β) t j k)

/-- The source-level form of `residualIdentity`, with the last-iterate
error and the explicitly defined `d_m`. -/
def sourceResidualIdentity (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (κm κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Prop :=
  residualIdentity I hΦ m κm (T (Nstar β))
    (sourceErrorD I hΦ m κm (T (Nstar β)))
    (iterateError I hΦ m κm κprev T)
    (streamVel (Φ m)) t x

end AVenhance.Infra.Section5

end
