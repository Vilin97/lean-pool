/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.OperationLevels

/-!
# Injective parent maps below the selected level

Every newly created lower node lies strictly above the selected anchor's
level. Thus nodes at or below that level come from upper copies, on which
the parent map is injective. Complete refinement additionally removes the
upper anchor, so no such low node can have the selected anchor as parent.
-/

namespace EGZ

namespace TwoLayer

variable {α : Type*} [SemilatticeSup α]

/-- Forgetting the layer is injective on upper-layer nodes. -/
theorem projection_injOn_nonzero (anchor : α) :
    Set.InjOn (projection anchor) {x : Node anchor | x.1.2 ≠ 0} := by
  intro x hx y hy hxy
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · have hx1 : x.1.2 = 1 := by have := x.1.2.isLt; change x.1.2 ≠ 0 at hx; omega
    have hy1 : y.1.2 = 1 := by have := y.1.2.isLt; change y.1.2 ≠ 0 at hy; omega
    exact hx1.trans hy1.symm

end TwoLayer

namespace FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

theorem reducedSubdivisionMap_node_injective (Φ : FlagDecomposition p d f) (hp : Odd p) :
    Function.Injective (Φ.reducedSubdivisionMap hp).node := Subtype.val_injective

theorem PrunedWeights.cleanedSubdivisionMap_node_injective {Φ : FlagDecomposition p d f}
    (D : PrunedWeights Φ) (hp : Odd p) : Function.Injective (D.cleanedSubdivisionMap hp).node :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

namespace FaceRefinement

variable (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart
      ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective
      ((Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem normalized_low_layer_ne_zero (hΓ : Γ ≠ ⊤) (L : ℕ) (hL : L ≤ Φ.level anchor)
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node)
    (hx : (normalized Φ anchor Γ hp C hmod hcenter).level x ≤ L) : x.1.1.1.2 ≠ 0 := by
  intro hz
  have hproper : Γ.carrier ⊂ (Φ.flag.polytope anchor).carrier :=
    Set.ssubset_iff_subset_ne.mpr ⟨Γ.subset_polytope, fun h ↦ hΓ (RationalPolytope.Face.ext h)⟩
  have hlt := normalized_lower_level_lt Φ anchor Γ hp C hmod hcenter hproper x hz
  omega

/-- No two output nodes at or below the selected level share an old
parent. This does not require minimality of the input. -/
theorem normalized_parent_injOn_low (hΓ : Γ ≠ ⊤) (L : ℕ) (hL : L ≤ Φ.level anchor) :
    Set.InjOn (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node
      {x | (normalized Φ anchor Γ hp C hmod hcenter).level x ≤ L} := by
  intro x hx y hy hxy
  have hx0 := normalized_low_layer_ne_zero Φ anchor Γ hp C hmod hcenter hΓ L hL x hx
  have hy0 := normalized_low_layer_ne_zero Φ anchor Γ hp C hmod hcenter hΓ L hL y hy
  have h := TwoLayer.projection_injOn_nonzero anchor hx0 hy0 hxy
  exact Subtype.ext (Subtype.ext h)

end FaceRefinement

namespace CompletePreparation

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem normalized_low_layer_ne_zero (hcount : 0 < D.count) (L : ℕ) (hL : L ≤ Φ.level anchor)
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node)
    (hx : (D.normalized hp hδ hsmall C hmod hcenter).level x ≤ L) : x.1.1.1.2 ≠ 0 := by
  intro hz
  have hlt := D.normalized_lower_level_lt hp hδ hsmall C hmod hcenter hcount x hz
  omega

theorem normalized_parent_injOn_low (hcount : 0 < D.count) (L : ℕ) (hL : L ≤ Φ.level anchor) :
    Set.InjOn (D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node
      {x | (D.normalized hp hδ hsmall C hmod hcenter).level x ≤ L} := by
  intro x hx y hy hxy
  have hx0 := D.normalized_low_layer_ne_zero hp hδ hsmall C hmod hcenter hcount L hL x hx
  have hy0 := D.normalized_low_layer_ne_zero hp hδ hsmall C hmod hcenter hcount L hL y hy
  have hparent : TwoLayer.projection (D.prunedAnchor hp hδ hsmall) x.1.1 =
      TwoLayer.projection (D.prunedAnchor hp hδ hsmall) y.1.1 := Subtype.ext hxy
  have h := TwoLayer.projection_injOn_nonzero (D.prunedAnchor hp hδ hsmall) hx0 hy0 hparent
  exact Subtype.ext (Subtype.ext h)

/-- Complete refinement deletes the old upper anchor, and all its new
lower copies have larger level. Hence the anchor has no low-level child. -/
theorem normalized_low_parent_ne_anchor (hcount : 0 < D.count) (L : ℕ)
    (hL : L ≤ Φ.level anchor)
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node)
    (hx : (D.normalized hp hδ hsmall C hmod hcenter).level x ≤ L) :
    (D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x ≠ anchor := by
  intro heq
  have hx0 := D.normalized_low_layer_ne_zero hp hδ hsmall C hmod hcenter hcount L hL x hx
  have hx1 : x.1.1.1.2 = 1 := by have := x.1.1.1.2.isLt; omega
  apply D.normalized_node_ne_upperAnchor hp hδ hsmall C hmod hcenter x
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext heq
  · exact hx1

end CompletePreparation
end FlagDecomposition
end EGZ
