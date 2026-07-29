/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaDisk
public import LeanPool.Odlyzko.ExplicitFormula.WeightedRectangleArgumentPrinciple

/-!
# Completed Zeta Rectangle

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed dedekind zeta zeros in closed rectangle used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindZetaZerosInClosedRectangle
    (a b u v : ℝ) : Finset ℂ := by
  classical
  exact (completedDedekindZetaZeroDivisor_support_inter_compact_finite K
      (S := Icc a b ×ℂ Icc u v)
      (isCompact_Icc.reProdIm isCompact_Icc)).toFinset

omit [IsTotallyComplex K] in
theorem mem_completedDedekindZetaZerosInClosedRectangle_iff
    {a b u v : ℝ} {z : ℂ} :
    z ∈ completedDedekindZetaZerosInClosedRectangle K a b u v ↔
      z ∈ Icc a b ×ℂ Icc u v ∧
        z ∈ (completedDedekindZetaZeroDivisor K).support := by
  classical
  simp [completedDedekindZetaZerosInClosedRectangle]

theorem poleClearedCompletedDedekindZetaContinuation_eq_zero_of_mem_support
    {z : ℂ} (hz : z ∈ (completedDedekindZetaZeroDivisor K).support) :
    poleClearedCompletedDedekindZetaContinuation K z = 0 := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hanalytic : AnalyticAt ℂ Ξ z :=
    analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K z (mem_univ z)
  by_contra hne
  have horder0 : meromorphicOrderAt Ξ z = (0 : WithTop ℤ) := by
    rw [hanalytic.meromorphicOrderAt_eq,
      hanalytic.analyticOrderAt_eq_zero.mpr hne]
    simp
  rw [meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_eq_divisor K z]
    at horder0
  simp_all

theorem rectangleIntegral_mul_logDeriv_poleClearedCompletedDedekindZetaContinuation
    {h : ℂ → ℂ} {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v)
    (hh : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ h z)
    (hboundary : ∀ z ∈ Icc a b ×ℂ Icc u v,
      (z.re = a ∨ z.re = b ∨ z.im = u ∨ z.im = v) →
      poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    rectangleIntegral
        (fun z ↦ h z *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) z)
        (a + u * I) (b + v * I) =
      (2 * Real.pi * I) *
        ∑ p ∈ completedDedekindZetaZerosInClosedRectangle K a b u v,
          h p * (completedDedekindZetaZeroDivisor K p : ℂ) := by
  classical
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  let S := completedDedekindZetaZerosInClosedRectangle K a b u v
  have hS : ∀ p ∈ S,
      a < p.re ∧ p.re < b ∧ u < p.im ∧ p.im < v := by
    intro p hp
    have hp' :=
      (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hp
    have hpzero : Ξ p = 0 :=
      poleClearedCompletedDedekindZetaContinuation_eq_zero_of_mem_support K hp'.2
    rcases hp'.1 with ⟨⟨hpa, hpb⟩, ⟨hpu, hpv⟩⟩
    grind
  apply rectangleIntegral_mul_logDeriv_eq_two_pi_I_mul_sum hab huv hS
  · intro z _
    exact analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K z (mem_univ z)
  · simp_all
  · intro z hz hz0
    exact (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mpr
      ⟨hz, mem_completedDedekindZetaZeroDivisor_support_of_eq_zero K hz0⟩
  · intro p _
    exact
      meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_eq_divisor K p

end NumberField.Odlyzko
