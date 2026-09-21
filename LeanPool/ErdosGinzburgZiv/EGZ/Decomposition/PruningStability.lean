/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Completeness

/-!
# Completeness after pruning local weights

The cumulative atoms at a node form a subset of all local atoms.  Hence
their mass loss is at most the global retained mass loss.  This connects the
gap-pruning estimate to the thickness estimate at every old large node.
-/

open scoped BigOperators

namespace EGZ

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

/-- Cumulative mass is the mass of the local atoms based below the node. -/
theorem natMass_cumulativeWeight (pieces : F.Node → FpCoord p d → ℕ)
    (x : F.Node) :
    natMass (cumulativeWeight pieces x) =
      natMassOn (fun a : F.Node × FpCoord p d ↦ pieces a.1 a.2)
        {a | a.1 ≤ x} := by
  classical
  unfold natMass cumulativeWeight natMassOn
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Loss from a cumulative weight is bounded by loss from all local atoms. -/
theorem cumulativeWeight_mass_loss_le
    {pieces pieces' : F.Node → FpCoord p d → ℕ}
    (hle : ∀ x v, pieces' x v ≤ pieces x v) (x : F.Node) :
    natMass (cumulativeWeight pieces x) - natMass (cumulativeWeight pieces' x) ≤
      natMass (retainedWeight pieces) - natMass (retainedWeight pieces') := by
  rw [natMass_cumulativeWeight, natMass_cumulativeWeight,
    natMass_retainedWeight, natMass_retainedWeight]
  exact natMassOn_loss_le (fun a : F.Node × FpCoord p d ↦ hle a.1 a.2)
    {a | a.1 ≤ x}

/-- Real-valued form of the cumulative mass-loss bound, ready for relative
loss estimates. -/
theorem cumulativeWeight_mass_loss_le_real
    {pieces pieces' : F.Node → FpCoord p d → ℕ}
    (hle : ∀ x v, pieces' x v ≤ pieces x v) (x : F.Node) :
    (natMass (cumulativeWeight pieces x) : ℝ) - natMass (cumulativeWeight pieces' x) ≤
      (natMass (retainedWeight pieces) : ℝ) - natMass (retainedWeight pieces') := by
  rw [natMass_cumulativeWeight, natMass_cumulativeWeight,
    natMass_retainedWeight, natMass_retainedWeight]
  exact natMassOn_loss_le_real (fun a : F.Node × FpCoord p d ↦ hle a.1 a.2)
    {a | a.1 ≤ x}

end FlagDecompositionRaw

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- Pruning at most `α` of the original retained mass preserves thickness
at an old `ε`-large node, with deterioration at most `α / ε`. -/
theorem cumulativeWeight_thick_of_pruning (Φ : FlagDecomposition p d f)
    (hp : Odd p) {pieces : Φ.flag.Node → FpCoord p d → ℕ}
    {x : Φ.flag.Node} {t : ℕ} {δ α ε : ℝ}
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    (hthick : IsThickAlong (Φ.cumulativeWeight x) ξ t δ)
    (hle : ∀ y v, pieces y v ≤ Φ.localWeight y v)
    (hε : 0 < ε) (hα : 0 ≤ α) (hlarge : Φ.IsLargeElement ε x)
    (hloss : (Φ.retainedMass : ℝ) -
      natMass (FlagDecompositionRaw.retainedWeight pieces) ≤ α * Φ.retainedMass)
    (hδ : 0 ≤ δ - α / ε) :
    IsThickAlong (FlagDecompositionRaw.cumulativeWeight pieces x) ξ t (δ - α / ε) := by
  apply hthick.of_pruning
    (fun v ↦ FlagDecompositionRaw.cumulativeWeight_mono hle x v) hε hα
    ((Φ.isLargeElement_iff_natMass hp ε x).mp hlarge)
  · exact (FlagDecompositionRaw.cumulativeWeight_mass_loss_le_real hle x).trans hloss
  · exact hδ

/-- Every functional required for completeness remains thick after the
same global pruning, before the surviving flag is repackaged. -/
theorem IsCompleteElement.thick_of_pruning {Φ : FlagDecomposition p d f}
    {x : Φ.flag.Node} {t : ℕ} {δ α ε : ℝ}
    (hcomplete : Φ.IsCompleteElement x t δ) (hp : Odd p)
    {pieces : Φ.flag.Node → FpCoord p d → ℕ}
    (hle : ∀ y v, pieces y v ≤ Φ.localWeight y v)
    (hε : 0 < ε) (hα : 0 ≤ α) (hlarge : Φ.IsLargeElement ε x)
    (hloss : (Φ.retainedMass : ℝ) -
      natMass (FlagDecompositionRaw.retainedWeight pieces) ≤ α * Φ.retainedMass)
    (hδ : 0 ≤ δ - α / ε)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p)
    (hξ : Φ.representation.NonconstantOnFibers x ξ) :
    IsThickAlong (FlagDecompositionRaw.cumulativeWeight pieces x) ξ t (δ - α / ε) :=
  Φ.cumulativeWeight_thick_of_pruning hp (hcomplete ξ hξ) hle hε hα hlarge hloss hδ

end FlagDecomposition

end EGZ
