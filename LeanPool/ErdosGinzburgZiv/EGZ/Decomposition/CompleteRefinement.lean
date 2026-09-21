/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompleteBounds
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Thickness

/-!
# The complete-element refinement

The prepared lower layer acquires the chosen slab coordinates and is put in
minimal lattice coordinates. Its anchor is complete by maximality of the
thin directions. Passing to the face index of its whole polytope supplies a
reduced complete representative with exactly the same cumulative function.
-/

namespace EGZ.FlagDecomposition.CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- Augmented refinement in the chosen integral charts. -/
noncomputable abbrev refined : FlagDecomposition p d f :=
  Augmented.decomposition (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
    (D.extra_antitone hp hδ hsmall) C hmod hcenter

theorem refined_isMinimal : (D.refined hp hδ hsmall C hmod hcenter).IsMinimal :=
  Augmented.decomposition_isMinimal _ _ _ _ _ _ _ _

theorem refined_cumulativeWeight (x : (D.split hp hδ hsmall).flag.Node) :
    (D.refined hp hδ hsmall C hmod hcenter).cumulativeWeight x =
      (D.split hp hδ hsmall).cumulativeWeight x := rfl

theorem refined_retainedMass :
    (D.refined hp hδ hsmall C hmod hcenter).retainedMass =
      (D.split hp hδ hsmall).retainedMass := rfl

/-- The lower anchor is complete after adjoining all chosen directions. -/
theorem refined_lowerAnchor_isCompleteElement :
    (D.refined hp hδ hsmall C hmod hcenter).IsCompleteElement
      (D.lowerAnchor hp hδ hsmall) (t (D.count + 1)) δ := by
  intro η hη
  obtain ⟨v, w, hv, hw, hmap, hη⟩ := hη
  have hvold := Augmented.representation_space_le_original (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall)
    C hmod (D.lowerAnchor hp hδ hsmall) hv
  have hwold := Augmented.representation_space_le_original (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall)
    C hmod (D.lowerAnchor hp hδ hsmall) hw
  have haug := (Augmented.representation_map_eq_iff (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall)
    C hmod (D.lowerAnchor hp hδ hsmall) v w hv hw).mp hmap
  have hold : Φ.representation.map anchor v = Φ.representation.map anchor w := by
    have hfirst := congrArg
      (Coord.first ((D.split hp hδ hsmall).flag.rank (D.lowerAnchor hp hδ hsmall))
        (D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall))) haug
    simp only [Augmented.map, Coord.first_append] at hfirst
    change (D.split hp hδ hsmall).representation.map (D.lowerAnchor hp hδ hsmall) v =
      (D.split hp hδ hsmall).representation.map (D.lowerAnchor hp hδ hsmall) w at hfirst
    rwa [D.lowerAnchor_map hp hδ hsmall] at hfirst
  have hdir : ∀ i, i < D.count → D.chain.direction i v = D.chain.direction i w := by
    intro i hi
    have hlast := congrArg
      (Coord.last ((D.split hp hδ hsmall).flag.rank (D.lowerAnchor hp hδ hsmall))
        (D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall))) haug
    have hindex : i < D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall) := by
      rwa [D.extra_lowerAnchor hp hδ hsmall]
    have heq := congrFun hlast (⟨i, hindex⟩ : Fin _)
    simpa only [Augmented.map, Coord.last_append, AffineMap.pi_apply] using heq
  change IsThickAlong ((D.split hp hδ hsmall).cumulativeWeight
    (D.lowerAnchor hp hδ hsmall)) η (t (D.count + 1)) δ
  rw [D.lowerAnchor_cumulativeWeight hp hδ hsmall]
  exact D.chain.thick_slabIntersection_of_augmented_fibre Φ.representation anchor
    hδ D.maximal hvold hwold hold hdir hη

/-- A reduced node below the lower anchor with the same cumulative weight. -/
noncomputable def completeNode : (D.refined hp hδ hsmall C hmod hcenter).flag.Node :=
  (D.refined hp hδ hsmall C hmod hcenter).faceIndex (D.lowerAnchor hp hδ hsmall) ⊤

theorem completeNode_le_lowerAnchor :
    D.completeNode hp hδ hsmall C hmod hcenter ≤ D.lowerAnchor hp hδ hsmall :=
  (D.refined hp hδ hsmall C hmod hcenter).faceIndex_le _ _

theorem completeNode_isReduced :
    (D.refined hp hδ hsmall C hmod hcenter).IsReducedElement
      (D.completeNode hp hδ hsmall C hmod hcenter) :=
  (D.refined hp hδ hsmall C hmod hcenter).isReducedElement_faceIndex _ _

theorem completeNode_cumulativeWeight :
    (D.refined hp hδ hsmall C hmod hcenter).cumulativeWeight
        (D.completeNode hp hδ hsmall C hmod hcenter) =
      restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet := by
  rw [completeNode,
    (D.refined hp hδ hsmall C hmod hcenter).cumulativeWeight_faceIndex_top hp]
  exact D.lowerAnchor_cumulativeWeight hp hδ hsmall

theorem completeNode_isCompleteElement :
    (D.refined hp hδ hsmall C hmod hcenter).IsCompleteElement
      (D.completeNode hp hδ hsmall C hmod hcenter) (t (D.count + 1)) δ :=
  (D.refined hp hδ hsmall C hmod hcenter).isCompleteElement_faceIndex_top hp
    (D.refined_isMinimal hp hδ hsmall C hmod hcenter) _
    (D.refined_lowerAnchor_isCompleteElement hp hδ hsmall C hmod hcenter)

theorem refined_upperAnchor_not_isReducedElement :
    ¬ (D.refined hp hδ hsmall C hmod hcenter).IsReducedElement (D.upperAnchor hp hδ hsmall) := by
  rw [Augmented.decomposition_isReducedElement_iff]
  exact D.upperAnchor_not_isReducedElement hp hδ hsmall

theorem refined_retainedMass_loss_le :
    (Φ.retainedMass : ℝ) - (D.refined hp hδ hsmall C hmod hcenter).retainedMass ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) :=
  D.retainedMass_loss_le hp hδ hsmall

theorem refined_card_le :
    @Fintype.card (D.refined hp hδ hsmall C hmod hcenter).flag.Node
      (D.refined hp hδ hsmall C hmod hcenter).flag.nodeFintype ≤
        2 * Fintype.card Φ.flag.Node := D.card_le hp hδ hsmall

theorem refined_isKBounded {B : ℕ}
    (hB : ∀ x (q : IntCoord (C x).rank),
      q.real ∈ (((D.diagram hp hδ hsmall).chartedFlag C).polytope x).carrier →
        latticeSupNorm q ≤ B) :
    (D.refined hp hδ hsmall C hmod hcenter).IsKBounded (fun _ ↦ B) := hB

/-- Subdivision map from the augmented refinement back to the original decomposition. -/
noncomputable def refinedSubdivisionMap :
    SubdivisionMap Φ (D.refined hp hδ hsmall C hmod hcenter) :=
  (D.subdivisionMap hp hδ hsmall).comp
    (Augmented.subdivisionMap (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction
      hp (D.extra_antitone hp hδ hsmall) C hmod hcenter)

include hδ in
/-- An incomplete anchor forces the construction to add at least one new
direction whenever the first chosen width dominates its requested width. -/
theorem count_pos_of_not_complete (T : ℕ) (hwidth : T ≤ t 1)
    (hnot : ¬ Φ.IsCompleteElement anchor T δ) : 0 < D.count := by
  apply D.chain.length_pos_of_exists D.maximal
  simp only [IsCompleteElement, IsThickAlong, not_forall, not_not] at hnot
  obtain ⟨η, hη, hthin⟩ := hnot
  refine ⟨η, ?_, ?_⟩
  · intro hmem
    exact ((Φ.representation.mem_fiberConstantSubmodule_iff anchor η).mp hmem) hη
  · exact (hthin.mono_width hwidth).mono_error (by norm_num; linarith)

end EGZ.FlagDecomposition.CompletePreparation
