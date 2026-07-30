/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
public import LeanPool.Odlyzko.ExplicitFormula.WeightedDiskArgumentPrinciple
public import LeanPool.Odlyzko.ExplicitFormula.WeightedRectangleArgumentPrinciple
public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.LogDerivativeResidue

/-!
# Completed Zeta Rectangle

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex Filter NumberField
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem analyticOnNhd_poleClearedCompletedDedekindZetaContinuation :
    AnalyticOnNhd ℂ
      (poleClearedCompletedDedekindZetaContinuation K) Set.univ :=
  DifferentiableOn.analyticOnNhd
    (differentiable_poleClearedCompletedDedekindZetaContinuation K).differentiableOn
    isOpen_univ

open Classical in
theorem meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_ne_top
    (s : ℂ) :
    meromorphicOrderAt
      (poleClearedCompletedDedekindZetaContinuation K) s ≠ ⊤ := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hmero : MeromorphicOn Ξ Set.univ :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).meromorphicOn
  have htwo : meromorphicOrderAt Ξ (2 : ℂ) ≠ ⊤ := by
    have hne : Ξ (2 : ℂ) ≠ 0 :=
      poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
        (by norm_num)
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hmero (2 : ℂ) (Set.mem_univ _))).mpr
    exact
      ((analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
        (2 : ℂ) (Set.mem_univ _)).continuousAt.eventually_ne hne).filter_mono
        nhdsWithin_le_nhds
  exact hmero.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ s) htwo

open Classical in
theorem meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_nonneg
    (s : ℂ) :
    0 ≤ meromorphicOrderAt
      (poleClearedCompletedDedekindZetaContinuation K) s :=
  (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
    s (Set.mem_univ s)).meromorphicOrderAt_nonneg

open Classical in
/-- A completed dedekind zeta zero divisor used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindZetaZeroDivisor :
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
  MeromorphicOn.divisor
    (poleClearedCompletedDedekindZetaContinuation K) Set.univ

omit [IsTotallyComplex K] in
open Classical in
theorem completedDedekindZetaZeroDivisor_support_inter_compact_finite
    {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ (completedDedekindZetaZeroDivisor K).support).Finite := by
  classical
  let D := completedDedekindZetaZeroDivisor K
  have hloc :
      ∀ x ∈ S, ∃ V : Set ℂ, V ∈ 𝓝 x ∧
        Set.Finite (V ∩ D.support) := by
    intro x _
    rcases D.supportLocallyFiniteWithinDomain x (Set.mem_univ x) with
      ⟨V, hV, hfin⟩
    grind
  choose V hVnhds hVfin using hloc
  rcases hS.elim_nhds_subcover'
      (U := fun x hx ↦ V x hx)
      (hU := fun x hx ↦ hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      S ∩ D.support ⊆
        ⋃ x ∈ t, (V (x : ℂ) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyS, hyD⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : ℂ) x.2 := ht hyS
    simp_all
  have hfinite :
      Set.Finite (⋃ x ∈ t,
        (V (x : ℂ) x.2 ∩ D.support)) := by
    refine (t.finite_toSet).biUnion ?_
    simp_all
  exact hfinite.subset hsub

end NumberField.Odlyzko

end

section

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

end

section

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

end
