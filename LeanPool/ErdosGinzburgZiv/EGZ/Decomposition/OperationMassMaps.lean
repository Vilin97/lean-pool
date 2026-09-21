/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMap
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RechartPreservation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDecomposition
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LowerTransfer
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapCleanup

/-! # Coordinate and mass maps for the elementary constructions -/

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

noncomputable def reducedStableNodeMap (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : (Φ.reduced hp).flag.Node) : StableNodeMap Φ (Φ.reduced hp) x.val x where
  coord := IntegralAffineMap.id _
  polytope_mem := fun _ h ↦ h
  cumulative_le := by rw [Φ.reduced_cumulativeWeight]
  map_eq := fun _ _ ↦ rfl
  mass_loss_le := by
    rw [Φ.reduced_cumulativeWeight, Φ.reduced_retainedMass]
    simp

namespace PrunedWeights

variable {Φ : FlagDecomposition p d f} (D : Φ.PrunedWeights) (hp : Odd p)

noncomputable def rebuiltStableNodeMap (x : (D.rebuilt hp).flag.Node) :
    StableNodeMap Φ (D.rebuilt hp) x.val x where
  coord := IntegralAffineMap.id _
  polytope_mem := fun _ h ↦ D.rebuilt_polytope_subset hp x h
  cumulative_le := by
    rw [(D.rebuildData hp).decomposition_cumulativeWeight]
    exact FlagDecompositionRaw.cumulativeWeight_mono D.weight_le x.val
  map_eq := fun _ _ ↦ rfl
  mass_loss_le := by
    rw [(D.rebuildData hp).decomposition_cumulativeWeight]
    change (natMass (FlagDecompositionRaw.cumulativeWeight Φ.localWeight x.val) : ℝ) -
      natMass (FlagDecompositionRaw.cumulativeWeight D.weight x.val) ≤ _
    have hret : (D.rebuilt hp).retainedMass =
        natMass (FlagDecompositionRaw.retainedWeight D.weight) :=
      congrArg natMass (D.rebuildData hp).decomposition_retainedWeight
    rw [hret]
    exact FlagDecompositionRaw.cumulativeWeight_mass_loss_le_real D.weight_le x.val

noncomputable def cleanedStableNodeMap (x : (D.cleaned hp).flag.Node) :
    StableNodeMap Φ (D.cleaned hp) x.val.val x :=
  (D.rebuiltStableNodeMap hp x.val).comp ((D.rebuilt hp).reducedStableNodeMap hp x)

end PrunedWeights

namespace Rechart

variable (Φ : FlagDecomposition p d f)
    (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
    [Fact p.Prime] (hp : Odd p)
    (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

noncomputable def stableNodeMap (x : Φ.flag.Node) :
    StableNodeMap Φ (decomposition Φ C hp hinj hcenter) x x where
  coord := chart Φ C x
  polytope_mem := fun _ h ↦ chart_mem_polytope Φ C x h
  cumulative_le := by rw [decomposition_cumulativeWeight]
  map_eq v hv := by
    rw [decomposition_cumulativeWeight] at hv
    exact chart_map Φ C hp hinj x v (subset_affineSpan _ _ hv)
  mass_loss_le := by rw [decomposition_cumulativeWeight, decomposition_retainedMass]; simp

end Rechart

namespace FaceRefinement

variable (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (selected : FpCoord p d → Prop) (hp : Odd p)

noncomputable def upperStableNodeMap (x : Φ.flag.Node) :
    StableNodeMap Φ (decomposition Φ anchor selected hp) x (upper Φ anchor selected hp x) where
  coord := IntegralAffineMap.id _
  polytope_mem := by
    intro q hq
    change q ∈ (Φ.flag.polytope x).carrier
    change q ∈ ((decomposition Φ anchor selected hp).flag.polytope
      (upper Φ anchor selected hp x)).carrier at hq
    rwa [upper_polytope] at hq
  cumulative_le := by rw [upper_cumulativeWeight]
  map_eq := fun _ _ ↦ rfl
  mass_loss_le := by rw [upper_cumulativeWeight, retainedMass]; simp

end FaceRefinement

namespace LowerTransfer

variable (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node) (hp : Odd p)

noncomputable def stableNodeMap (x : (decomposition Φ anchor hp).flag.Node) :
    StableNodeMap Φ (decomposition Φ anchor hp) x.val.val.1 x where
  coord := IntegralAffineMap.id _
  polytope_mem := fun _ h ↦ (FaceRefinement.subdivisionMap Φ anchor (fun _ ↦ True) hp).polytope_mem x h
  cumulative_le := by rw [cumulativeWeight_projection]
  map_eq := fun _ _ ↦ rfl
  mass_loss_le := by rw [cumulativeWeight_projection, FaceRefinement.retainedMass]; simp

end LowerTransfer

namespace Augmented

variable (Φ : FlagDecomposition p d f) (e : Φ.flag.Node → ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (hp : Odd p) (he : Antitone e)
    (C : ∀ x, IntegerLatticeChart ((diagram Φ e ξ hp he).support x))
    [Fact p.Prime]
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

noncomputable def stableNodeMap (x : Φ.flag.Node) :
    StableNodeMap Φ (decomposition Φ e ξ hp he C hmod hcenter) x x where
  coord := forget Φ e ξ hp he C x
  polytope_mem := fun _ h ↦ forget_mem_polytope Φ e ξ hp he C x h
  cumulative_le := by rw [decomposition_cumulativeWeight]
  map_eq v hv := by
    rw [decomposition_cumulativeWeight] at hv
    exact forget_representation_map Φ e ξ hp he C hmod x v (subset_affineSpan _ _ hv)
  mass_loss_le := by rw [decomposition_cumulativeWeight, decomposition_retainedMass]; simp

end Augmented
end EGZ.FlagDecomposition
