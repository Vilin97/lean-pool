/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Divisorial gonality as a natural number

The dependency already defines `gonality_leq G k` and a noncomputable
`gonality h_conn : ℤ` (`ChipFiringWithLean/RiemannRoch.lean`).  The
treewidth/gonality chain wants to compare gonality with `treewidth`, which is a
`ℕ`, so this module packages the same invariant as an `sInf` over `ℕ` and proves
the bridges in both directions.

* `gonalitySet G : Set ℕ` — degrees of **effective** divisors of rank at least
  one.  Adding effectivity does not change the set of achievable degrees (a
  divisor of rank `≥ 1` is winnable, and both degree and rank are linear
  equivalence invariants), but it is the form the van Dobben de Bruyn--Gijswijt
  argument consumes.
* `divisorialGonality G := sInf (gonalitySet G)`.  Nonemptiness of `gonalitySet`
  for connected `G` (`gonalitySet_nonempty`, via the dependency's
  `gonality_leq_genus_add_one`) is what makes the `sInf` meaningful rather than
  the `sInf ∅ = 0` default; every statement that needs it takes
  `graph_connected G`.
* Bridges: `BNExists_one_divisorialGonality`,
  `divisorialGonality_le_of_BNExists`, and
  `gonality_eq_divisorialGonality` (the dependency's `ℤ`-valued `gonality` is
  the coercion of this one).
-/

namespace Utilities.Gonality

open Finset

variable {G : CFGraph}

/-! ## Effective representatives -/

/-- A divisor of rank at least one has an effective representative of the same
degree and rank. -/
theorem exists_effective_of_rank_ge_one {D : CFDiv G} (hD : rank G D ≥ 1) :
    ∃ E : CFDiv G, effective E ∧ deg E = deg D ∧ rank G E ≥ 1 := by
  have hwin : winnable G D :=
    (rank_nonneg_iff_winnable G D).mp ((rank_geq_iff G D 0).mpr (by omega))
  obtain ⟨E, hEeff, hequiv⟩ := (winnable_iff_exists_effective G D).mp hwin
  refine ⟨E, hEeff, (linear_equiv_preserves_deg G D E hequiv).symm, ?_⟩
  rw [← Utilities.rank_eq_of_linear_equiv G hequiv]
  exact hD

/-- A divisor of rank at least one has degree at least one. -/
theorem one_le_deg_of_rank_ge_one {D : CFDiv G} (hD : rank G D ≥ 1) : 1 ≤ deg D :=
  rank_le_degree G D 1 (by norm_num) ((rank_geq_iff G D 1).mpr hD)

/-! ## The gonality set and `divisorialGonality` -/

/-- The degrees of the effective divisors of rank at least one. -/
def gonalitySet (G : CFGraph) : Set ℕ :=
  {d : ℕ | ∃ D : CFDiv G, effective D ∧ deg D = (d : ℤ) ∧ rank G D ≥ 1}

/-- The **divisorial gonality** of `G`: the least degree of an effective divisor
of rank at least one, as a natural number. -/
noncomputable def divisorialGonality (G : CFGraph) : ℕ :=
  sInf (gonalitySet G)

/-- Membership in `gonalitySet` from an explicit witness. -/
theorem mem_gonalitySet {d : ℕ} {D : CFDiv G} (hEff : effective D)
    (hDeg : deg D = (d : ℤ)) (hRank : rank G D ≥ 1) : d ∈ gonalitySet G :=
  ⟨D, hEff, hDeg, hRank⟩

/-- On a connected graph there is an effective divisor of rank at least one (of
degree `genus G + 1`), so `divisorialGonality` is an infimum over a nonempty
set. -/
theorem gonalitySet_nonempty (h_conn : graph_connected G) :
    (gonalitySet G).Nonempty := by
  obtain ⟨D, hRank, hDeg⟩ := gonality_leq_genus_add_one h_conn
  obtain ⟨E, hEeff, hEdeg, hErank⟩ := exists_effective_of_rank_ge_one hRank
  have hpos : 0 ≤ deg E := le_trans (by norm_num) (one_le_deg_of_rank_ge_one hErank)
  exact ⟨(deg E).toNat, E, hEeff, by rw [Int.toNat_of_nonneg hpos], hErank⟩

/-- Any effective divisor of rank at least one bounds the gonality. -/
theorem divisorialGonality_le {d : ℕ} {D : CFDiv G} (hEff : effective D)
    (hDeg : deg D = (d : ℤ)) (hRank : rank G D ≥ 1) :
    divisorialGonality G ≤ d :=
  Nat.sInf_le (mem_gonalitySet hEff hDeg hRank)

/-- The gonality is realized by an actual divisor. -/
theorem exists_divisor_of_divisorialGonality (h_conn : graph_connected G) :
    ∃ D : CFDiv G, effective D ∧ deg D = (divisorialGonality G : ℤ) ∧
      rank G D ≥ 1 :=
  Nat.sInf_mem (gonalitySet_nonempty h_conn)

/-- The gonality of a connected graph is at least one. -/
theorem one_le_divisorialGonality (h_conn : graph_connected G) :
    1 ≤ divisorialGonality G := by
  obtain ⟨D, _, hDeg, hRank⟩ := exists_divisor_of_divisorialGonality h_conn
  have := one_le_deg_of_rank_ge_one hRank
  omega

/-- `divisorialGonality G ≤ genus G + 1` for connected `G`. -/
theorem divisorialGonality_le_genus_add_one (h_conn : graph_connected G) :
    (divisorialGonality G : ℤ) ≤ genus G + 1 := by
  obtain ⟨D, hRank, hDeg⟩ := gonality_leq_genus_add_one h_conn
  obtain ⟨E, hEeff, hEdeg, hErank⟩ := exists_effective_of_rank_ge_one hRank
  have hpos : 0 ≤ deg E := le_trans (by norm_num) (one_le_deg_of_rank_ge_one hErank)
  have hle : divisorialGonality G ≤ (deg E).toNat :=
    divisorialGonality_le hEeff (by rw [Int.toNat_of_nonneg hpos]) hErank
  have : ((deg E).toNat : ℤ) = genus G + 1 := by
    rw [Int.toNat_of_nonneg hpos, hEdeg, hDeg]
  omega

/-! ## Bridges to `BNExists` and to the dependency's `gonality` -/

/-- The gonality divisor is a rank-one Brill--Noether witness. -/
theorem BNExists_one_divisorialGonality (h_conn : graph_connected G) :
    BNExists G 1 (divisorialGonality G : ℤ) := by
  obtain ⟨D, _, hDeg, hRank⟩ := exists_divisor_of_divisorialGonality h_conn
  exact ⟨D, hDeg, hRank⟩

/-- Any rank-one Brill--Noether witness bounds the gonality. -/
theorem divisorialGonality_le_of_BNExists {d : ℤ} (h : BNExists G 1 d) :
    (divisorialGonality G : ℤ) ≤ d := by
  obtain ⟨D, hDeg, hRank⟩ := h
  obtain ⟨E, hEeff, hEdeg, hErank⟩ := exists_effective_of_rank_ge_one hRank
  have hpos : 0 ≤ deg E := le_trans (by norm_num) (one_le_deg_of_rank_ge_one hErank)
  have hle : divisorialGonality G ≤ (deg E).toNat :=
    divisorialGonality_le hEeff (by rw [Int.toNat_of_nonneg hpos]) hErank
  have hcast : ((deg E).toNat : ℤ) = d := by rw [Int.toNat_of_nonneg hpos, hEdeg, hDeg]
  omega

/-- The dependency's predicate `gonality_leq` holds at the gonality. -/
theorem gonality_leq_divisorialGonality (h_conn : graph_connected G) :
    gonality_leq G (divisorialGonality G : ℤ) := by
  obtain ⟨D, _, hDeg, hRank⟩ := exists_divisor_of_divisorialGonality h_conn
  exact ⟨D, hRank, hDeg⟩

/-- The set the dependency takes an `sInf` over is bounded below by `1`. -/
theorem bddBelow_gonality_leq (G : CFGraph) :
    BddBelow {k : ℤ | gonality_leq G k} := by
  refine ⟨1, ?_⟩
  rintro k ⟨D, hRank, hDeg⟩
  rw [← hDeg]
  exact one_le_deg_of_rank_ge_one hRank

/-- **The two gonalities agree**: the dependency's `ℤ`-valued `gonality` is the
coercion of `divisorialGonality`. -/
theorem gonality_eq_divisorialGonality (h_conn : graph_connected G) :
    gonality h_conn = (divisorialGonality G : ℤ) := by
  have hne : {k : ℤ | gonality_leq G k}.Nonempty :=
    ⟨genus G + 1, gonality_leq_genus_add_one h_conn⟩
  refine le_antisymm ?_ ?_
  · exact csInf_le (bddBelow_gonality_leq G) (gonality_leq_divisorialGonality h_conn)
  · refine le_csInf hne ?_
    rintro k ⟨D, hRank, hDeg⟩
    exact divisorialGonality_le_of_BNExists ⟨D, hDeg, hRank⟩

end Utilities.Gonality
