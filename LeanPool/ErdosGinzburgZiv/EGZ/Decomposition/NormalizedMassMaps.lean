/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.OperationMassMaps
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedFace
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedComplete
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NormalizedGap

/-! # Stable mass maps for normalized refinement steps -/

@[expose] public section

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

namespace PrunedWeights

variable {Φ : FlagDecomposition p d f} (D : Φ.PrunedWeights) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart ((D.cleaned hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective ((Rechart.chart (D.cleaned hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- The stable map from a normalized pruned node to its original ancestor. -/
noncomputable def normalizedStableNodeMap (x : (D.normalized hp C hmod hcenter).flag.Node) :
    StableNodeMap Φ (D.normalized hp C hmod hcenter)
      ((D.normalizedSubdivisionMap hp C hmod hcenter).node x) x :=
  (D.cleanedStableNodeMap hp x).comp
    (Rechart.stableNodeMap (D.cleaned hp) C hp hmod hcenter x)

@[simp]
theorem normalizedStableNodeMap_real (x : (D.normalized hp C hmod hcenter).flag.Node) :
    (D.normalizedStableNodeMap hp C hmod hcenter x).coord.real =
      (D.normalizedSubdivisionMap hp C hmod hcenter).fibre x := rfl

end PrunedWeights

namespace CompletePreparation

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- The stable node map induced by the splitting stage of complete preparation. -/
noncomputable def splitStableNodeMap (x : (D.split hp hδ hsmall).flag.Node) :
    StableNodeMap Φ (D.split hp hδ hsmall) ((D.subdivisionMap hp hδ hsmall).node x) x :=
  ((LocalizedPruning.prunedWeights Φ anchor D.selectedSet
      (D.selected_nonzero hδ hsmall)).rebuiltStableNodeMap hp x.val.val.1).comp
    (LowerTransfer.stableNodeMap (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp x)

/-- The stable node map after splitting and recharting the completion refinement. -/
noncomputable def refinedStableNodeMap (x : (D.refined hp hδ hsmall C hmod hcenter).flag.Node) :
    StableNodeMap Φ (D.refined hp hδ hsmall C hmod hcenter)
      ((D.refinedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) x :=
  (D.splitStableNodeMap hp hδ hsmall x).comp
    (Augmented.stableNodeMap (D.split hp hδ hsmall) (D.extra hp hδ hsmall)
      D.chain.direction hp (D.extra_antitone hp hδ hsmall) C hmod hcenter x)

/-- The stable node map from a normalized complete refinement to the original decomposition. -/
noncomputable def normalizedStableNodeMap
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) :
    StableNodeMap Φ (D.normalized hp hδ hsmall C hmod hcenter)
      ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) x :=
  (D.refinedStableNodeMap hp hδ hsmall C hmod hcenter x.val).comp
    ((D.refined hp hδ hsmall C hmod hcenter).reducedStableNodeMap hp x)

@[simp]
theorem normalizedStableNodeMap_real
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) :
    (D.normalizedStableNodeMap hp hδ hsmall C hmod hcenter x).coord.real =
      (D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).fibre x := by
  ext q
  rfl

end CompletePreparation

namespace FaceRefinement

variable (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart
      ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective ((Rechart.chart
      (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- The stable node map for an upper-layer node of the normalized face refinement. -/
noncomputable def normalizedUpperStableNodeMap
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node)
    (hx : x.val.val.val.2 = 1) :
    StableNodeMap Φ (normalized Φ anchor Γ hp C hmod hcenter)
      ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x) x := by
  have hu : x.val = upper Φ anchor (Φ.faceSelector anchor Γ) hp x.val.val.val.1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl hx
  refine {
    coord := Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x.val
    polytope_mem := fun _ h ↦
      (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).polytope_mem x h
    cumulative_le := ?_
    map_eq := ?_
    mass_loss_le := ?_ }
  · rw [(minimalized Φ anchor Γ hp C hmod hcenter).reduced_cumulativeWeight]
    change (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).cumulativeWeight x.val ≤ _
    rw [hu, upper_cumulativeWeight]
    exact le_rfl
  · intro v hv
    apply Rechart.chart_map (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C hp hmod x.val v
    apply subset_affineSpan
    rwa [(minimalized Φ anchor Γ hp C hmod hcenter).reduced_cumulativeWeight] at hv
  · rw [normalized_retainedMass,
      (minimalized Φ anchor Γ hp C hmod hcenter).reduced_cumulativeWeight]
    change (natMass (Φ.cumulativeWeight x.val.val.val.1) : ℝ) -
      natMass ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).cumulativeWeight x.val) ≤ _
    rw [hu, upper_cumulativeWeight]
    simp only [Fin.isValue, sub_self, tsub_le_iff_right, zero_add, Nat.cast_le]
    exact le_rfl

@[simp]
theorem normalizedUpperStableNodeMap_real
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node)
    (hx : x.val.val.val.2 = 1) :
    (normalizedUpperStableNodeMap Φ anchor Γ hp C hmod hcenter x hx).coord.real =
      (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre x := by
  ext q
  rfl

end FaceRefinement
end EGZ.FlagDecomposition
