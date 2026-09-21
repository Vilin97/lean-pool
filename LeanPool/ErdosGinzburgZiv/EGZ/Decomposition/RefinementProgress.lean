/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedOperations
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedMassMaps
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageOperations
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceMassChain

/-!
# Progress certificates for face and complete-element refinements

The concrete normalized operations satisfy the iteration's level, stable
mass transport, parent injectivity, resolution, and numerical requirements.
-/

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (s : State p d f) {R : ℕ}

noncomputable abbrev faceState {anchor : s.decomposition.flag.Node}
    {Γ : (s.decomposition.flag.polytope anchor).Face}
    (D : NormalizedFaceStep s.decomposition anchor Γ s.radius R) : State p d f where
  decomposition := D.decomposition
  radius := D.radius
  radius_pos := s.radius_pos.trans D.radius_ge
  minimal := D.isMinimal
  reduced := D.isReduced
  bounded := D.bounded

noncomputable abbrev completeState {anchor : s.decomposition.flag.Node}
    {g : ℕ → ℕ} {δ : ℝ} {hδ : 0 ≤ δ} {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep s.decomposition anchor g s.radius R δ hδ hsmall) : State p d f where
  decomposition := D.decomposition
  radius := D.radius
  radius_pos := s.radius_pos.trans D.radius_ge
  minimal := D.isMinimal
  reduced := D.isReduced
  bounded := D.bounded

/-- A valid face event supplies every field of a progress certificate. -/
noncomputable def faceProgress {anchor : s.decomposition.flag.Node}
    {Γ : (s.decomposition.flag.polytope anchor).Face} {ε δ : ℝ} {g : ℕ → ℕ}
    (D : NormalizedFaceStep s.decomposition anchor Γ s.radius R)
    (hvalid : (State.Event.face anchor Γ : s.Event).Valid ε δ g)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) : Progress s (faceState s D) ε δ g := by
  have hΓ : Γ ≠ ⊤ := by
    intro heq
    apply hvalid.2
    rw [heq]
    exact s.decomposition.isRealizedFace_top anchor
  have hlayer : ∀ y : D.decomposition.flag.Node,
      D.decomposition.level y ≤ s.decomposition.level anchor → y.val.val.val.2 = 1 := by
    intro y hy
    have hne := FaceRefinement.normalized_low_layer_ne_zero s.decomposition anchor Γ
      D.odd D.charts D.modInjective D.centered hΓ (s.decomposition.level anchor) le_rfl y hy
    have := y.val.val.val.2.isLt
    omega
  refine {
    event := .face anchor Γ
    valid := hvalid
    subdivision := D.subdivisionMap
    level_parent := FaceRefinement.normalized_level_le s.decomposition anchor Γ
      D.odd D.charts D.modInjective D.centered
    stable := fun y hy ↦ FaceRefinement.normalizedUpperStableNodeMap s.decomposition anchor Γ
      D.odd D.charts D.modInjective D.centered y (hlayer y hy)
    stable_real := fun y hy ↦ FaceRefinement.normalizedUpperStableNodeMap_real s.decomposition
      anchor Γ D.odd D.charts D.modInjective D.centered y (hlayer y hy)
    parent_injective := FaceRefinement.normalized_parent_injOn_low s.decomposition anchor Γ
      D.odd D.charts D.modInjective D.centered hΓ (s.decomposition.level anchor) le_rfl
    resolves := ?_
    radius_le := D.radius_ge
    card_le := D.card_le
    mass_le := D.retainedMass.le
    mass_loss_le := ?_ }
  · refine ⟨D.targetNode hΓ (s.reduced anchor), D.target_projection hΓ (s.reduced anchor), ?_, ?_⟩
    · exact FaceRefinement.normalizedTargetNode_level_eq s.decomposition anchor Γ
        D.odd D.charts D.modInjective D.centered s.minimal hΓ (s.reduced anchor)
    · intro hne
      have heq : D.subdivisionMap.face (D.targetNode hΓ (s.reduced anchor))
          (s.decomposition.faceAtNode Γ (D.target_projection hΓ (s.reduced anchor))) hne =
          D.targetFace hΓ (s.reduced anchor) := by
        apply RationalPolytope.Face.ext
        rfl
      rw [heq]
      exact D.target_isRealized hΓ (s.reduced anchor)
  · change (s.decomposition.retainedMass : ℝ) - D.decomposition.retainedMass ≤ _
    rw [D.retainedMass, sub_self]
    positivity

/-- A valid incomplete-element event forces a positive number of added
directions, even though the actual output radius is chosen with the charts. -/
theorem completeStep_count_pos {anchor : s.decomposition.flag.Node}
    {ε δ : ℝ} {g : ℕ → ℕ} {hδ : 0 ≤ δ} {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep s.decomposition anchor g s.radius R δ hδ hsmall)
    (hvalid : (State.Event.complete anchor : s.Event).Valid ε δ g) (hg : Monotone g) :
    0 < D.preparation.count := by
  by_contra! hzero
  have hz : D.preparation.count = 0 := Nat.eq_zero_of_le_zero hzero
  have hwidth : g s.radius ≤ D.widths 1 :=
    (hg D.radius_ge).trans (by simpa only [hz, zero_add] using D.desired_width)
  have hpos := D.preparation.count_pos_of_not_complete hδ (g s.radius) hwidth hvalid.2
  omega

/-- The complete-element construction supplies stable mass maps at all
nodes and removes every low-level child of the selected anchor. -/
noncomputable def completeProgress {anchor : s.decomposition.flag.Node}
    {ε δ : ℝ} {g : ℕ → ℕ} {hδ : 0 ≤ δ} {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep s.decomposition anchor g s.radius R δ hδ hsmall)
    (hvalid : (State.Event.complete anchor : s.Event).Valid ε δ g)
    (hε : 0 ≤ ε) (hg : Monotone g) : Progress s (completeState s D) ε δ g := by
  have hcount := completeStep_count_pos s D hvalid hg
  refine {
    event := .complete anchor
    valid := hvalid
    subdivision := D.subdivisionMap
    level_parent := D.preparation.normalized_level_le D.odd hδ hsmall D.charts
      D.modInjective D.centered
    stable := fun y _ ↦ D.preparation.normalizedStableNodeMap D.odd hδ hsmall D.charts
      D.modInjective D.centered y
    stable_real := fun y _ ↦ D.preparation.normalizedStableNodeMap_real D.odd hδ hsmall D.charts
      D.modInjective D.centered y
    parent_injective := D.preparation.normalized_parent_injOn_low D.odd hδ hsmall D.charts
      D.modInjective D.centered hcount (s.decomposition.level anchor) le_rfl
    resolves := D.preparation.normalized_low_parent_ne_anchor D.odd hδ hsmall D.charts
      D.modInjective D.centered hcount (s.decomposition.level anchor) le_rfl
    radius_le := D.radius_ge
    card_le := D.card_le
    mass_le := ?_
    mass_loss_le := ?_ }
  · let M := D.preparation.normalizedStableNodeMap D.odd hδ hsmall D.charts
      D.modInjective D.centered D.targetNode
    have hnode := Nat.cast_le (α := ℝ).mpr (natMass_mono M.cumulative_le)
    have hmass := M.mass_loss_le
    have hle : (D.decomposition.retainedMass : ℝ) ≤ s.decomposition.retainedMass := by linarith
    exact_mod_cast hle
  · have hcum : (natMass (s.decomposition.cumulativeWeight anchor) : ℝ) ≤
        s.decomposition.retainedMass := by
      exact_mod_cast s.decomposition.cumulativeMass_le_retainedMass anchor
    have hcoef : 0 ≤ (3 : ℝ) ^ (d + 1) * δ := by positivity
    have hmain := D.mass_loss.trans (mul_le_mul_of_nonneg_left hcum hcoef)
    have hextra : 0 ≤ ε * δ ^ 2 * s.decomposition.retainedMass := by positivity
    change (s.decomposition.retainedMass : ℝ) - D.decomposition.retainedMass ≤ _
    nlinarith

end EGZ.FlagDecomposition.Iteration
