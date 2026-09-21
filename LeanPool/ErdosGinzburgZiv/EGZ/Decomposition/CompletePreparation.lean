/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LocalizedPruning
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LowerTransfer
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedCompleteness

/-!
# Preparing a complete-element refinement

Choose the maximal thin directions, prune only below the selected anchor,
and transfer its surviving local mass to a lower layer. This produces an
actual flag decomposition, with controlled mass loss and a non-reduced old
upper anchor, before adjoining the new slab coordinates.
-/

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

/-- A bounded chain of thin directions used to prepare a complete refinement. -/
structure CompletePreparation (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (t : ℕ → ℕ) (δ : ℝ) where
  /-- Number of selected thin directions. -/
  count : ℕ
  count_le : count ≤ d
  /-- Chain witnessing thinness in the selected directions at their prescribed scales. -/
  chain : DirectionChain (Φ.representation.fiberConstantSubmodule anchor)
    (fun i ξ ↦ IsThinAlong (Φ.cumulativeWeight anchor) ξ (t (i + 1))
      ((3 : ℝ) ^ (i + 1) * δ)) count
  maximal : ∀ ξ, ξ ∉ chain.space count →
    IsThickAlong (Φ.cumulativeWeight anchor) ξ (t (count + 1)) ((3 : ℝ) ^ (count + 1) * δ)

theorem nonempty_completePreparation (Φ : FlagDecomposition p d f)
    (anchor : Φ.flag.Node) (t : ℕ → ℕ) (δ : ℝ) :
    Nonempty (CompletePreparation Φ anchor t δ) := by
  obtain ⟨k, hk, D, hmax⟩ := exists_maximal_thinDirections Φ.representation anchor
    (Φ.cumulativeWeight anchor) t δ
  exact ⟨⟨k, hk, D, hmax⟩⟩

namespace CompletePreparation

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)

/-- Intersection of the slabs selected by the direction chain. -/
def selectedSet : Set (FpCoord p d) := slabIntersection D.count D.chain.direction t

theorem selected_nonzero (_hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1) :
    ∃ v, restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet v ≠ 0 := by
  apply D.chain.slabIntersection_nonzero hδ D.count_le hsmall
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty anchor
  obtain ⟨_, v, _, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff anchor q).mp
    ((Φ.liftedSupport_spec anchor q).mp hq)
  exact ⟨v, hv⟩

variable (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)

/-- Decomposition obtained by pruning to the selected slab intersection. -/
noncomputable abbrev pruned : FlagDecomposition p d f :=
  LocalizedPruning.decomposition Φ anchor D.selectedSet (D.selected_nonzero hp hδ hsmall) hp

/-- Distinguished anchor in the pruned decomposition. -/
noncomputable abbrev prunedAnchor : (D.pruned hp hδ hsmall).flag.Node :=
  LocalizedPruning.anchorNode Φ anchor D.selectedSet (D.selected_nonzero hp hδ hsmall) hp

/-- Two-layer decomposition obtained by splitting the pruned anchor. -/
noncomputable abbrev split : FlagDecomposition p d f :=
  LowerTransfer.decomposition (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp

/-- Lower copy of the anchor after splitting. -/
noncomputable abbrev lowerAnchor : (D.split hp hδ hsmall).flag.Node :=
  LowerTransfer.lowerAnchor (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp

/-- Upper copy of the anchor after splitting. -/
noncomputable abbrev upperAnchor : (D.split hp hδ hsmall).flag.Node :=
  LowerTransfer.upper (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp
    (D.prunedAnchor hp hδ hsmall)

theorem lowerAnchor_cumulativeWeight :
    (D.split hp hδ hsmall).cumulativeWeight (D.lowerAnchor hp hδ hsmall) =
      restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet := by
  rw [LowerTransfer.lowerAnchor_cumulativeWeight]
  exact LocalizedPruning.cumulativeWeight_anchorNode _ _ _ _ _

theorem lowerAnchor_space :
    (D.split hp hδ hsmall).representation.space (D.lowerAnchor hp hδ hsmall) =
      Φ.representation.space anchor := rfl

theorem lowerAnchor_map :
    (D.split hp hδ hsmall).representation.map (D.lowerAnchor hp hδ hsmall) =
      Φ.representation.map anchor := rfl

theorem upperAnchor_not_isReducedElement :
    ¬ (D.split hp hδ hsmall).IsReducedElement (D.upperAnchor hp hδ hsmall) :=
  LowerTransfer.upperAnchor_not_isReducedElement _ _ _

theorem retainedMass_loss :
    (Φ.retainedMass : ℝ) - (D.split hp hδ hsmall).retainedMass =
      (natMass (Φ.cumulativeWeight anchor) : ℝ) -
        natMass (restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet) := by
  rw [FaceRefinement.retainedMass (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall)
    (fun _ ↦ True) hp]
  exact LocalizedPruning.decomposition_retainedMass_loss _ _ _ _ _

theorem retainedMass_loss_le :
    (Φ.retainedMass : ℝ) - (D.split hp hδ hsmall).retainedMass ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) := by
  rw [D.retainedMass_loss hp hδ hsmall]
  exact D.chain.slabIntersection_loss_le_dimension hδ D.count_le

theorem card_le :
    @Fintype.card (D.split hp hδ hsmall).flag.Node
      (D.split hp hδ hsmall).flag.nodeFintype ≤ 2 * Fintype.card Φ.flag.Node := by
  apply (FaceRefinement.card_le (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall)
    (fun _ ↦ True) hp).trans
  apply Nat.mul_le_mul_left
  exact ((LocalizedPruning.prunedWeights Φ anchor D.selectedSet
    (D.selected_nonzero hp hδ hsmall)).rebuildData hp).card_decomposition_le

/-- Forget the lower-layer labels and recover a proper point of the old flag. -/
noncomputable def subdivisionMap : SubdivisionMap Φ (D.split hp hδ hsmall) :=
  ((LocalizedPruning.prunedWeights Φ anchor D.selectedSet
    (D.selected_nonzero hp hδ hsmall)).rebuiltSubdivisionMap hp).comp
      (FaceRefinement.subdivisionMap (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall)
        (fun _ ↦ True) hp)

/-- Number of additional coordinates assigned to each split node. -/
noncomputable abbrev extra : (D.split hp hδ hsmall).flag.Node → ℕ :=
  LowerTransfer.extra (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp D.count

theorem extra_antitone : Antitone (D.extra hp hδ hsmall) :=
  LowerTransfer.extra_antitone _ _ _ _

theorem extra_lowerAnchor : D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall) = D.count :=
  LowerTransfer.extra_lowerAnchor _ _ _ _

theorem extra_upperAnchor : D.extra hp hδ hsmall (D.upperAnchor hp hδ hsmall) = 0 :=
  LowerTransfer.extra_upper _ _ _ _ _

end CompletePreparation

end EGZ.FlagDecomposition
