/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CanonicalConfiguration

/-!
# Planar Fox--Neuwirth strata

The stratum of a barred permutation is described directly in the labelled configuration space.
Labels in one block have equal first coordinate and occur in the recorded vertical order; labels
in different blocks occur in the recorded left-to-right order.
-/

namespace NRR

variable {p : ℕ}

namespace BarredPermutation

 theorem blockIndex_mono
    (c : BarredPermutation p) {i j : Fin p}
    (hij : (c.rank i).1 ≤ (c.rank j).1) :
    c.blockIndex i ≤ c.blockIndex j := by
  unfold blockIndex
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

 theorem blockIndex_lt_of_rank_lt_of_not_sameBlock
    (c : BarredPermutation p) {i j : Fin p}
    (hij : (c.rank i).1 < (c.rank j).1)
    (hblock : ¬ c.SameBlock i j) :
    c.blockIndex i < c.blockIndex j := by
  have hle : c.blockIndex i ≤ c.blockIndex j :=
    c.blockIndex_mono (Nat.le_of_lt hij)
  exact lt_of_le_of_ne hle (by
    intro h
    exact hblock h)

/-- Membership in the open Fox--Neuwirth stratum represented by `c`. -/
def InStratum (c : BarredPermutation p) (s : Config p) : Prop :=
  ∀ i j, (c.rank i).1 < (c.rank j).1 →
    if c.SameBlock i j then
      s.pts i 0 = s.pts j 0 ∧ s.pts i 1 < s.pts j 1
    else
      s.pts i 0 < s.pts j 0

 theorem canonicalConfig_mem_stratum (c : BarredPermutation p) :
    c.InStratum c.canonicalConfig := by
  intro i j hij
  by_cases hblock : c.SameBlock i j
  · rw [if_pos hblock]
    constructor
    · rw [canonicalConfig_pts, canonicalConfig_pts,
        canonicalPoint_x, canonicalPoint_x]
      exact congrArg (fun x : Nat => (x : ℝ)) hblock
    · rw [canonicalConfig_pts, canonicalConfig_pts,
        canonicalPoint_y, canonicalPoint_y]
      exact Nat.cast_lt.mpr hij
  · rw [if_neg hblock]
    rw [canonicalConfig_pts, canonicalConfig_pts,
      canonicalPoint_x, canonicalPoint_x]
    exact Nat.cast_lt.mpr (c.blockIndex_lt_of_rank_lt_of_not_sameBlock hij hblock)

/-- Relabelling transports a stratum to the relabelled stratum. -/
theorem inStratum_relabel_iff
    (σ : Equiv.Perm (Fin p))
    (c : BarredPermutation p) (s : Config p) :
    (c.relabel σ).InStratum (Config.relabel σ s) ↔
      c.InStratum s := by
  constructor
  · intro h i j hij
    have hij' : ((c.relabel σ).rank (σ i)).1 <
        ((c.relabel σ).rank (σ j)).1 := by simpa using hij
    have h' := h (σ i) (σ j) hij'
    simpa [InStratum] using h'
  · intro h i j hij
    have hij' : (c.rank (σ.symm i)).1 <
        (c.rank (σ.symm j)).1 := by simpa using hij
    have h' := h (σ.symm i) (σ.symm j) hij'
    simpa [InStratum] using h'

end BarredPermutation

end NRR
