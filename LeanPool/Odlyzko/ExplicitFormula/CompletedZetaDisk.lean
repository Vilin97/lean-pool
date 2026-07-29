/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaZeros
public import LeanPool.Odlyzko.ExplicitFormula.WeightedDiskArgumentPrinciple

/-!
# Completed Zeta Disk

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Metric NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem mem_completedDedekindZetaZeroDivisor_support_of_eq_zero
    {z : ℂ}
    (hz : poleClearedCompletedDedekindZetaContinuation K z = 0) :
    z ∈ (completedDedekindZetaZeroDivisor K).support := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have han : AnalyticAt ℂ Ξ z :=
    analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K z (mem_univ z)
  rw [Function.mem_support]
  intro hdiv
  have hord :
      meromorphicOrderAt Ξ z =
        (((completedDedekindZetaZeroDivisor K) z : ℤ) : WithTop ℤ) := by
    have hmero : MeromorphicOn Ξ univ :=
      (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).meromorphicOn
    rw [completedDedekindZetaZeroDivisor,
      hmero.divisor_apply (mem_univ z)]
    exact (WithTop.coe_untop₀_of_ne_top
      (meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_ne_top K z)).symm
  have hord0 : meromorphicOrderAt Ξ z = 0 := by simp_all
  rw [han.meromorphicOrderAt_eq] at hord0
  have hne : analyticOrderAt Ξ z ≠ 0 :=
    han.analyticOrderAt_ne_zero.mpr hz
  simp_all

theorem meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_eq_divisor
    (z : ℂ) :
    meromorphicOrderAt (poleClearedCompletedDedekindZetaContinuation K) z =
      ((completedDedekindZetaZeroDivisor K z : ℤ) : WithTop ℤ) := by
  have hmero :
      MeromorphicOn (poleClearedCompletedDedekindZetaContinuation K) univ :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).meromorphicOn
  rw [completedDedekindZetaZeroDivisor,
    hmero.divisor_apply (mem_univ z)]
  exact (WithTop.coe_untop₀_of_ne_top
    (meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_ne_top K z)).symm

end NumberField.Odlyzko
