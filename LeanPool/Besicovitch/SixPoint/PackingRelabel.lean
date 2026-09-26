/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Packing

/-!
# Relabelling supported packings

A color-preserving permutation transports a packing and preserves its radius sum and score.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch.SixPointPacking

/-- Pull the support back along the relabelling permutation. -/
def relabelSupportEquiv (support : Finset SixPointIndex)
    (permutation : SixPointIndex ≃ SixPointIndex) :
    (support.map permutation.toEmbedding : Finset SixPointIndex) ≃ support where
  toFun index := ⟨permutation.symm index, by
    obtain ⟨source, hsource, heq⟩ := Finset.mem_map.1 index.2
    simpa only [← heq, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hsource⟩
  invFun index := ⟨permutation index, Finset.mem_map.2 ⟨index, index.2, rfl⟩⟩
  left_inv index := Subtype.ext (permutation.apply_symm_apply index)
  right_inv index := Subtype.ext (permutation.symm_apply_apply index)

/-- Transport a packing along a color-preserving permutation of its centers. -/
def relabel {source target : SixPointConfiguration} (packing : SixPointPacking source)
    (permutation : SixPointIndex ≃ SixPointIndex)
    (hcolor : ∀ index, (permutation index).1 = index.1)
    (hconfiguration : ∀ index, source index.1 index.2 =
      target (permutation index).1 (permutation index).2) : SixPointPacking target where
  support := packing.support.map permutation.toEmbedding
  meets_color color := by
    obtain ⟨label, hlabel⟩ := packing.meets_color color
    refine ⟨(permutation (color, label)).2, Finset.mem_map.2 ⟨(color, label), hlabel, ?_⟩⟩
    exact Prod.ext (hcolor _) rfl
  radius index := packing.radius (relabelSupportEquiv packing.support permutation index)
  same_color_disjoint i j hij hsame := by
    let equivalence := relabelSupportEquiv packing.support permutation
    have hsame' : (equivalence i).1.1 = (equivalence j).1.1 := by
      have hi : i.1.1 = (permutation.symm i).1 := by
        simpa only [Equiv.apply_symm_apply] using hcolor (permutation.symm i)
      have hj : j.1.1 = (permutation.symm j).1 := by
        simpa only [Equiv.apply_symm_apply] using hcolor (permutation.symm j)
      exact hi.symm.trans (hsame.trans hj)
    have hp := packing.same_color_disjoint (equivalence i) (equivalence j)
      (fun heq ↦ hij (equivalence.injective heq)) hsame'
    simpa only [hconfiguration, equivalence, relabelSupportEquiv, Equiv.coe_fn_mk,
      Equiv.apply_symm_apply] using hp

variable {source target : SixPointConfiguration} (packing : SixPointPacking source)
    (permutation : SixPointIndex ≃ SixPointIndex)
    (hcolor : ∀ index, (permutation index).1 = index.1)
    (hconfiguration : ∀ index, source index.1 index.2 =
      target (permutation index).1 (permutation index).2)

/-- Relabelling preserves the sum of the supported radii. -/
theorem relabel_totalRadius :
    (packing.relabel permutation hcolor hconfiguration).totalRadius = packing.totalRadius := by
  unfold totalRadius
  rw [← Finset.univ_eq_attach, ← Finset.univ_eq_attach]
  exact Fintype.sum_equiv (relabelSupportEquiv packing.support permutation) _ _ (fun _ ↦ rfl)

/-- Relabelling preserves every contribution to the virtual diameter. -/
theorem relabel_virtualDiameter :
    (packing.relabel permutation hcolor hconfiguration).virtualDiameter =
      packing.virtualDiameter := by
  let equivalence := relabelSupportEquiv packing.support permutation
  have hpair (i j : (packing.relabel permutation hcolor hconfiguration).support) :
      dist (target i.1.1 i.1.2) (target j.1.1 j.1.2) +
        (packing.relabel permutation hcolor hconfiguration).radius i +
        (packing.relabel permutation hcolor hconfiguration).radius j =
      dist (source (equivalence i).1.1 (equivalence i).1.2)
        (source (equivalence j).1.1 (equivalence j).1.2) +
        packing.radius (equivalence i) + packing.radius (equivalence j) := by
    simp only [hconfiguration, equivalence, relabelSupportEquiv, Equiv.coe_fn_mk,
      Equiv.apply_symm_apply, relabel]
  apply le_antisymm
  · unfold virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    rw [hpair]
    exact packing.pair_le_virtualDiameter (equivalence i) (equivalence j)
  · unfold virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    have hp := (packing.relabel permutation hcolor hconfiguration).pair_le_virtualDiameter
      (equivalence.symm i) (equivalence.symm j)
    have hbound := (hpair (equivalence.symm i) (equivalence.symm j)).symm.trans_le hp
    simpa only [Equiv.apply_symm_apply, virtualDiameter] using hbound

/-- Relabelling preserves the score at every threshold. -/
theorem relabel_score (s : ℝ) :
    (packing.relabel permutation hcolor hconfiguration).score s = packing.score s := by
  simp only [score, relabel_totalRadius, relabel_virtualDiameter]

end LeanPool.Besicovitch.SixPointPacking
