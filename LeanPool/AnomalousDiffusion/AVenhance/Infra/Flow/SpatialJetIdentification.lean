/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetGlobal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FirstJet
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC1

/-! Identification of the first globally constructed jet with the spatial
Fréchet derivative of the original flow. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

/-- The first recursively constructed jet flow, started from the identity
jet, is exactly the established position/Jacobian augmented flow. -/
theorem spatialJetFlow_one_identity_eq_firstJetFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (t : ℝ) (x : Vec 2) (s : ℝ) :
    spatialJetFlow hb X hX 1 t (spatialJetIdentitySeed 1 x) s =
      firstJetFlow X t (spatialJetIdentitySeed 1 x) s := by
  have hX' : IsFlowOn b X := hX
  have hY₀ := spatialJetFlow_isFlow hb hX' 1
  have hY : IsFlowOn (firstJetField b) (spatialJetFlow hb X hX 1) := by
    rw [← spatialJetField_one_eq_firstJetField]
    exact hY₀
  have hZ := firstJetFlow_isFlow hb hX
  let a : ℝ := min s t
  let d : ℝ := max s t
  have hs : s ∈ Icc a d := by
    constructor
    · dsimp [a]
      exact min_le_left _ _
    · dsimp [d]
      exact le_max_left _ _
  have ht : t ∈ Icc a d := by
    constructor
    · dsimp [a]
      exact min_le_right _ _
    · dsimp [d]
      exact le_max_right _ _
  exact spatialJetField_flow_unique_on_window hb 1 hY hZ a d s hs
    (spatialJetIdentitySeed 1 x) t ht

/-- In coordinates, the first identity-seeded jet consists of the original
flow and its spatial derivative applied to the coordinate directions. -/
theorem spatialJetFlow_one_identity_components
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (t : ℝ) (x : Vec 2) (s : ℝ) :
    spatialJetFlow hb X hX 1 t (spatialJetIdentitySeed 1 x) s =
      (X t x s, fun i => fderiv ℝ (fun y => X t y s) x (Pi.single i 1)) := by
  rw [spatialJetFlow_one_identity_eq_firstJetFlow hb hX t x s,
    spatialJetIdentitySeed_one]
  rfl

end AVenhance.Infra.Flow
