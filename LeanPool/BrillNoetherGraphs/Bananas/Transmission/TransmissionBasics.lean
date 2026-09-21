/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankChipStep

/-!
# Basic periodicity lemmas for marked banana transmission

These lemmas are graph-independent.  They isolate the part of the paper's
torsion-periodicity argument that follows solely from linear equivalence,
before any banana rank computation is used.
-/

namespace Bananas

open Utilities

/-- Simultaneously increasing the two transmission coordinates by a torsion
order changes a marked twist by the principal divisor `k (u - v)`. -/
theorem linearEquiv_marked_twist_add_torsion
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (a b : ℤ) :
    linear_equiv M.graph
      (D + (a + k) • one_chip M.u - (b + k) • one_chip M.v)
      (D + a • one_chip M.u - b • one_chip M.v) := by
  rcases hk with ⟨_, hk⟩
  unfold linear_equiv at hk ⊢
  have hDifference :
      (D + a • one_chip M.u - b • one_chip M.v) -
          (D + (a + k) • one_chip M.u - (b + k) • one_chip M.v) =
        0 - (k : ℤ) • (one_chip M.u - one_chip M.v) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring_nf
    simp
  rw [hDifference]
  exact hk

/-- The ranks of corresponding marked twists are periodic at every torsion
witness. -/
theorem rank_marked_twist_add_torsion
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (a b : ℤ) :
    rank M.graph (D + (a + k) • one_chip M.u - (b + k) • one_chip M.v) =
      rank M.graph (D + a • one_chip M.u - b • one_chip M.v) :=
  rank_eq_of_linear_equiv M.graph
    (linearEquiv_marked_twist_add_torsion hk D a b)

/-- The only way the marked rank second difference can be negative.  This is
the rank-pattern criterion used throughout the paper's submodularity proofs. -/
theorem rankDelta_neg_iff_rank_pattern
    (M : TwiceMarked) (D : CFDiv M.graph) :
    rankDelta M D < 0 ↔
      rank M.graph D = rank M.graph (D - one_chip M.u) ∧
      rank M.graph D = rank M.graph (D - one_chip M.v) ∧
      rank M.graph D =
        rank M.graph (D - one_chip M.u - one_chip M.v) + 1 := by
  let Du : CFDiv M.graph := D - one_chip M.u
  let Dv : CFDiv M.graph := D - one_chip M.v
  let Duv : CFDiv M.graph := D - one_chip M.u - one_chip M.v
  have hDu_le : rank M.graph Du ≤ rank M.graph D := by
    have h := rank_add_one_chip_ge Du M.u (rank M.graph Du) le_rfl
    have heq : Du + one_chip M.u = D := by
      dsimp [Du]
      abel
    rwa [heq] at h
  have hDu_ge : rank M.graph Du ≥ rank M.graph D - 1 := by
    simpa [Du] using rank_sub_one_chip_ge_rank_sub_one D M.u
  have hDv_le : rank M.graph Dv ≤ rank M.graph D := by
    have h := rank_add_one_chip_ge Dv M.v (rank M.graph Dv) le_rfl
    have heq : Dv + one_chip M.v = D := by
      dsimp [Dv]
      abel
    rwa [heq] at h
  have hDv_ge : rank M.graph Dv ≥ rank M.graph D - 1 := by
    simpa [Dv] using rank_sub_one_chip_ge_rank_sub_one D M.v
  have hDuv_le_Du : rank M.graph Duv ≤ rank M.graph Du := by
    have h := rank_add_one_chip_ge Duv M.v (rank M.graph Duv) le_rfl
    have heq : Duv + one_chip M.v = Du := by
      dsimp [Duv, Du]
      abel
    rwa [heq] at h
  have hDuv_ge_Du : rank M.graph Duv ≥ rank M.graph Du - 1 := by
    have h := rank_sub_one_chip_ge_rank_sub_one Du M.v
    have heq : Du - one_chip M.v = Duv := by
      dsimp [Duv, Du]
    rwa [heq] at h
  have hDuv_le_Dv : rank M.graph Duv ≤ rank M.graph Dv := by
    have h := rank_add_one_chip_ge Duv M.u (rank M.graph Duv) le_rfl
    have heq : Duv + one_chip M.u = Dv := by
      dsimp [Duv, Dv]
      abel
    rwa [heq] at h
  have hDuv_ge_Dv : rank M.graph Duv ≥ rank M.graph Dv - 1 := by
    have h := rank_sub_one_chip_ge_rank_sub_one Dv M.u
    have heq : Dv - one_chip M.u = Duv := by
      dsimp [Duv, Dv]
      abel
    rwa [heq] at h
  dsimp [rankDelta, Du, Dv, Duv] at *
  constructor <;> intro h
  · omega
  · omega

/-- Because `AllSubmodular` quantifies over every divisor already, its
apparently two-level definition is equivalent to pointwise nonnegativity of
the marked rank second difference. -/
theorem allSubmodular_iff_rankDelta_nonneg (M : TwiceMarked) :
    AllSubmodular M ↔ ∀ D : CFDiv M.graph, 0 ≤ rankDelta M D := by
  constructor
  · intro h D
    simpa [Submodular, twist] using h D 0 0
  · intro h D a b
    exact h (twist M D a b)

/-- Failure of all-divisor submodularity has a single negative rank-difference
witness.  This is the form used by the theta and higher-genus classifications. -/
theorem not_allSubmodular_iff_exists_rankDelta_neg (M : TwiceMarked) :
    ¬ AllSubmodular M ↔ ∃ D : CFDiv M.graph, rankDelta M D < 0 := by
  rw [allSubmodular_iff_rankDelta_nonneg]
  push Not
  constructor <;> intro h
  · obtain ⟨D, hD⟩ := h
    exact ⟨D, by omega⟩
  · obtain ⟨D, hD⟩ := h
    exact ⟨D, by omega⟩

end Bananas
