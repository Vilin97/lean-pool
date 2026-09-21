/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedMassMaps
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedOperations

/-! # Gap cleanup as a certified iteration step -/

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (s : State p d f) {R : ℕ} {ε δ : ℝ}
    (D : NormalizedGapStep s.decomposition s.radius R (ε * δ ^ 2))

/-- Iteration state produced by the gap-cleanup data. -/
noncomputable def gapState : State p d f where
  decomposition := D.decomposition
  radius := D.radius
  radius_pos := s.radius_pos.trans D.radius_ge
  minimal := D.isMinimal
  reduced := D.isReduced
  bounded := D.bounded

theorem gapState_gapCondition {i : ℕ} (hi : 1 ≤ i)
    (hε : 0 ≤ ε)
    (hcard : Fintype.card s.decomposition.flag.Node ≤ 2 ^ (i - 1))
    (hretained : (natMass f : ℝ) / 2 ≤ s.decomposition.retainedMass)
    (hscale : δ ≤ ε * (3 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ i) :
    (gapState s D).GapCondition δ := by
  intro x
  have hgap : ε * δ ^ 2 * (2 * (D.radius : ℝ) + 1)⁻¹ ^ d *
      (Fintype.card s.decomposition.flag.Node : ℝ)⁻¹ * s.decomposition.retainedMass ≤
        (D.decomposition.gap x : ℝ) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc, mul_left_comm, mul_comm]
      using D.gap_bound x
  exact DecompositionParameters.gap_threshold_of_cleanup hi hε
    (by exact_mod_cast (gapState s D).radius_pos)
    (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card s.decomposition.flag.Node)
    (by exact_mod_cast hcard) (Nat.cast_nonneg _) hretained hscale hgap

/-- Certify progress of a gap cleanup that restores the gap condition. -/
noncomputable def gapProgress (_hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hvalid : ¬ s.GapCondition δ) (hgap : (gapState s D).GapCondition δ)
    (g : ℕ → ℕ) : Progress s (gapState s D) ε δ g where
  event := .gap
  valid := hvalid
  subdivision := D.subdivisionMap
  level_parent x :=
    (D.weights.normalizedStableNodeMap D.odd D.charts
      D.modInjective D.centered x).toNodeMassMap.level_le
      D.isMinimal
  stable x _ := D.weights.normalizedStableNodeMap D.odd D.charts D.modInjective D.centered x
  stable_real x _ :=
    D.weights.normalizedStableNodeMap_real D.odd D.charts D.modInjective D.centered x
  parent_injective := by
    intro x _ y _ hxy
    exact Subtype.ext (Subtype.ext hxy)
  resolves := hgap
  radius_le := D.radius_ge
  card_le := D.card_le.trans (Nat.le_mul_of_pos_left _ (by omega))
  mass_le := natMass_mono
    (D.weights.normalized_retainedWeight_le D.odd D.charts D.modInjective D.centered)
  mass_loss_le := by
    change (s.decomposition.retainedMass : ℝ) - D.decomposition.retainedMass ≤ _
    have hnonneg : 0 ≤ (3 : ℝ) ^ (d + 1) * δ * s.decomposition.retainedMass := by positivity
    nlinarith [D.mass_loss]

end EGZ.FlagDecomposition.Iteration
