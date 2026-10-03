/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityLower
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedFlux

/-! Quantitative drift-error pairing from actual velocity jets. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The scalar velocity product for a specified list of actual ordered splits. -/
def iterateVelocitySplit (P : List (List (Fin 2) × List (Fin 2)))
    (b : Vec 2 → Vec 2) (v : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  ∑ j : Fin 2, (P.map (fun p => iterateSpatialWord p.1 (fun y => b y j) x *
    spaceGrad (iterateSpatialWord p.2 v) x j)).sum

end AVenhance.Infra.Section4
