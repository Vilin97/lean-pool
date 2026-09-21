/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTimeShift

/-!
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Exit times are monotone in the set: a path leaves a larger set no earlier. -/
theorem exitTime_mono {U V : Set alpha} (hUV : U ⊆ V) (omega : ContinuousPath alpha) :
    exitTime U omega ≤ exitTime V omega := by
  rw [le_exitTime_iff]
  intro v hv
  exact exitTime_le_of_notMem U omega v (fun h ↦ hv (hUV h))

/-- Truncated exit times are monotone in the set. -/
theorem exitTimeTrunc_mono {U V : Set alpha} (hUV : U ⊆ V) (K : NNReal)
    (omega : ContinuousPath alpha) : exitTimeTrunc U K omega ≤ exitTimeTrunc V K omega := by
  rw [← WithTop.coe_le_coe, coe_exitTimeTrunc, coe_exitTimeTrunc]
  exact min_le_min_right _ (exitTime_mono hUV omega)

/-- An open exhaustion of the state space: an increasing sequence of open sets whose union is the
whole space. -/
structure IsOpenExhaustion (U : ℕ → Set alpha) : Prop where
  /-- Every member is open. -/
  isOpen : ∀ n, IsOpen (U n)
  /-- The sequence is increasing. -/
  monotone : Monotone U
  /-- The sequence covers the state space. -/
  iUnion_eq : ⋃ n, U n = Set.univ

/-- On a compact time interval, a continuous path eventually lies inside the members of an open
exhaustion, and its exit times are eventually larger than the interval's endpoint. -/
theorem IsOpenExhaustion.exists_lt_exitTime {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (omega : ContinuousPath alpha) (T : NNReal) :
    ∃ N, ∀ n ≥ N, (T : ℝ≥0∞) < exitTime (U n) omega := by
  have hcompact : IsCompact ((omega : NNReal → alpha) '' Set.Icc 0 T) :=
    isCompact_Icc.image omega.continuous
  have hcover : (omega : NNReal → alpha) '' Set.Icc 0 T ⊆ ⋃ n, U n := by
    rw [hU.iUnion_eq]
    exact Set.subset_univ _
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U hU.isOpen hcover
  refine ⟨s.sup id, fun n hn ↦ ?_⟩
  have hsub : (omega : NNReal → alpha) '' Set.Icc 0 T ⊆ U n := by
    refine hs.trans (Set.iUnion₂_subset fun i hi ↦ hU.monotone ?_)
    exact (Finset.le_sup (f := id) hi).trans hn
  by_contra hle
  rw [not_lt, exitTime_le_iff_mem_hitsSetBy (U n) (hU.isOpen n) T omega] at hle
  obtain ⟨t, ht⟩ := hle
  exact ht (hsub ⟨t, Set.mem_Icc.mpr ⟨zero_le, t.2⟩, rfl⟩)

/-- Along an open exhaustion the exit times of a continuous path tend to infinity. -/
theorem IsOpenExhaustion.tendsto_exitTime_atTop {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (omega : ContinuousPath alpha) :
    Tendsto (fun n ↦ exitTime (U n) omega) atTop (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro T
  obtain ⟨N, hN⟩ := hU.exists_lt_exitTime omega T
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

/-- Along an open exhaustion, every time is eventually below the exit time. -/
theorem IsOpenExhaustion.eventually_lt_exitTime {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (omega : ContinuousPath alpha) (t : NNReal) :
    ∀ᶠ n in atTop, (t : ℝ≥0∞) < exitTime (U n) omega :=
  Filter.eventually_atTop.mpr (hU.exists_lt_exitTime omega t)

/-- The exit times along an open exhaustion form a monotone sequence. -/
theorem IsOpenExhaustion.monotone_exitTime {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (omega : ContinuousPath alpha) : Monotone fun n ↦ exitTime (U n) omega :=
  fun _ _ hmn ↦ exitTime_mono (hU.monotone hmn) omega

/-- The supremum of the exit times along an open exhaustion is infinite. -/
theorem IsOpenExhaustion.iSup_exitTime {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (omega : ContinuousPath alpha) : ⨆ n, exitTime (U n) omega = ⊤ := by
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  refine iSup_le fun T ↦ ?_
  obtain ⟨N, hN⟩ := hU.exists_lt_exitTime omega T
  exact le_iSup_of_le N (by exact_mod_cast (hN N le_rfl).le)

end MarkovProcess.ContinuousPath
