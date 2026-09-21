/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CompletePreparation
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.AugmentedDiagram
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportParameters

/-!
# Bounds for the augmented completeness diagram

Only lower-layer nodes carry added slab coordinates, and all their cumulative
atoms lie in the selected slab intersection. Consequently the augmented
support has rank at most twice the ambient dimension and lies in the last
selected width box.
-/

open Classical

namespace EGZ.FlagDecomposition.CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)

theorem extra_le_count (x : (D.split hp hδ hsmall).flag.Node) :
    D.extra hp hδ hsmall x ≤ D.count := by
  change (if x.1.1.2 = 0 then D.count else 0) ≤ D.count
  split_ifs <;> omega

theorem selected_of_extra_pos (x : (D.split hp hδ hsmall).flag.Node)
    (hx : 0 < D.extra hp hδ hsmall x) (v : FpCoord p d)
    (hv : (D.split hp hδ hsmall).cumulativeWeight x v ≠ 0) : v ∈ D.selectedSet := by
  have hlayer : x.1.1.2 = 0 := by
    by_contra h
    change 0 < (if x.1.1.2 = 0 then D.count else 0) at hx
    rw [ite_eq_right h] at hx
    exact Nat.not_lt_zero _ hx
  have hbase : x.1.1.1 ≤ D.prunedAnchor hp hδ hsmall := x.1.2 hlayer
  rw [LowerTransfer.cumulativeWeight_projection] at hv
  rw [LocalizedPruning.cumulativeWeight_below Φ anchor D.selectedSet
    (D.selected_nonzero hp hδ hsmall) hp x.1.1.1 hbase] at hv
  by_contra h
  exact hv (ite_eq_right h)

theorem slabCoordinates_bound (ht : Monotone t)
    (htsmall : ∀ i : Fin D.count, 2 * t (i + 1) < p)
    (x : (D.split hp hδ hsmall).flag.Node) (v : FpCoord p d)
    (hv : (D.split hp hδ hsmall).cumulativeWeight x v ≠ 0) :
    latticeSupNorm (EGZ.slabCoordinates (D.extra hp hδ hsmall x) D.chain.direction v) ≤
      t D.count := by
  by_cases hlayer : x.1.1.2 = 0
  · have heq : D.extra hp hδ hsmall x = D.count := by
      change (if x.1.1.2 = 0 then D.count else 0) = D.count
      rw [ite_eq_left hlayer]
    rw [heq]
    by_cases hk : D.count = 0
    · rw [latticeSupNorm_le_iff]
      intro i
      have hi := i.isLt
      omega
    · apply EGZ.slabCoordinates_bound D.chain.direction t ht htsmall
      exact D.selected_of_extra_pos hp hδ hsmall x (by rw [heq]; omega) v hv
  · have heq : D.extra hp hδ hsmall x = 0 := by
      change (if x.1.1.2 = 0 then D.count else 0) = 0
      rw [ite_eq_right hlayer]
    rw [latticeSupNorm_le_iff]
    intro i
    have hi := i.isLt
    omega

theorem split_isKBounded {K : ℕ} (hK : Φ.IsKBounded (fun _ ↦ K)) :
    (D.split hp hδ hsmall).IsKBounded (fun _ ↦ K) := by
  intro x q hq
  have hold := (D.subdivisionMap hp hδ hsmall).polytope_mem x hq
  exact hK _ q hold

noncomputable abbrev diagram : LatticeSupportDiagram :=
  Augmented.diagram (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
    (D.extra_antitone hp hδ hsmall)

theorem diagram_rank_le (x : (D.diagram hp hδ hsmall).Node) :
    (D.diagram hp hδ hsmall).rank x ≤ 2 * d := by
  change (D.split hp hδ hsmall).flag.rank x + D.extra hp hδ hsmall x ≤ 2 * d
  have hr := (D.split hp hδ hsmall).representation.rank_le x
  have he := (D.extra_le_count hp hδ hsmall x).trans D.count_le
  omega

theorem diagram_support_bound {K : ℕ} (hK : Φ.IsKBounded (fun _ ↦ K))
    (ht : Monotone t) (hKt : K ≤ t D.count)
    (htsmall : ∀ i : Fin D.count, 2 * t (i + 1) < p)
    (x : (D.diagram hp hδ hsmall).Node)
    (q : IntCoord ((D.diagram hp hδ hsmall).rank x))
    (hq : q ∈ (D.diagram hp hδ hsmall).support x) : latticeSupNorm q ≤ t D.count := by
  have hbound := Augmented.support_bound (D.split hp hδ hsmall) (D.extra hp hδ hsmall)
    D.chain.direction hp (D.split_isKBounded hp hδ hsmall hK)
      (D.slabCoordinates_bound hp hδ hsmall ht htsmall) x q hq
  exact hbound.trans (max_le hKt le_rfl)

end EGZ.FlagDecomposition.CompletePreparation
